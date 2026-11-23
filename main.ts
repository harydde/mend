/**
 * mend — apply a patch to a tree of files.
 *
 * Usage: node main.ts [--check] [--strict] [--format=NAME] [PATCH]
 * PATCH defaults to stdin. See SPEC.md.
 *
 * Deterministic: no Date, no Math.random, no environment-dependent output.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'] as const;
type Format = (typeof FORMATS)[number];

class Exit2 extends Error {}
class Fail extends Error {
  kind: string;
  p: string;
  constructor(kind: string, p: string) {
    super(`${kind} ${p}`);
    this.kind = kind;
    this.p = p;
  }
}

function blank(l: string): boolean {
  return l.trim() === '';
}

// Trim only spaces and tabs from both ends (SPEC §5: "spaces and tabs").
function trimST(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}
// Trim only space characters from both ends (SPEC §6/§8: "surrounding
// spaces removed" — distinct from "whitespace" in §7/§8 and "spaces and
// tabs" in §5).
function trimSpaces(s: string): string {
  return s.replace(/^ +/, '').replace(/ +$/, '');
}
function trimEndST(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

// The patch's lines: the patch is split at \n, one trailing \r is removed
// from each line, and there is no empty piece after a final \n.
function patchLines(text: string): string[] {
  const ls = text.split('\n').map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
  if (ls.length > 0 && ls[ls.length - 1] === '') ls.pop();
  return ls;
}

// A path is safe when it is not empty, does not start with /, has no
// backslash, and every /-separated part is not empty and is neither . nor ..
function safe(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((part) => part !== '' && part !== '.' && part !== '..');
}

// ---------------------------------------------------------------- file model

// A file's line break is CRLF when its first \n follows a \r, else LF. The
// file is split at that break; a trailing empty piece after a final break is
// not a line; an empty file has no lines and no final break.
interface FileState {
  lines: string[];
  br: string; // '\r\n' or '\n'
  final: boolean; // the file ends with its line break
}

function splitFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', final: false };
  const firstNl = text.indexOf('\n');
  const br = firstNl > 0 && text[firstNl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const body = final ? text.slice(0, -br.length) : text;
  // Note: body '' (a file that is just one line break) splits to [''], one
  // empty line — only the truly empty file has no lines.
  return { lines: body.split(br), br, final };
}

function joinFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.final ? st.br : '');
}

// ---------------------------------------------------------------- matching (§5)

function leadWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndST(a) === trimEndST(b);
  return trimST(a) === trimST(b);
}

// The first tier with at least one occurrence wins; occurrences may overlap.
// When endAnchored, only occurrences ending at the file's last line count.
function findTier(
  lines: string[],
  o: string[],
  strict: boolean,
  from: number,
  endAnchored = false,
): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions: number[] = [];
    for (let i = from; i + o.length <= lines.length; i++) {
      if (endAnchored && i + o.length !== lines.length) continue;
      let ok = true;
      for (let j = 0; j < o.length; j++) {
        if (!lineEq(lines[i + j]!, o[j]!, t)) {
          ok = false;
          break;
        }
      }
      if (ok) positions.push(i);
    }
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

// First line at or after `from` equal to `anchor` at the first tier with one.
function findSingle(
  lines: string[],
  anchor: string,
  strict: boolean,
  from: number,
): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = from; i < lines.length; i++) {
      if (lineEq(lines[i]!, anchor, t)) return i;
    }
  }
  return null;
}

type Op = { k: 'ctx' | 'del' | 'add'; text: string };

// Build the replacement lines for ops matched at file position `pos`.
// Context lines are written as the file's own matched line. At tier 2, a
// non-empty, non-whitespace-only line of N starting with P (the leading
// spaces/tabs of O's first line) has P replaced by F (those of the file's
// first matched line).
function applyOps(fileLines: string[], pos: number, ops: Op[], tier: number): string[] {
  const out: string[] = [];
  let p = '';
  let f = '';
  if (tier === 2) {
    const o0 = ops.find((o) => o.k !== 'add');
    if (o0 !== undefined) {
      p = leadWs(o0.text);
      f = leadWs(fileLines[pos]!);
    }
  }
  let oi = 0;
  for (const op of ops) {
    if (op.k === 'ctx') {
      out.push(fileLines[pos + oi]!);
      oi++;
    } else if (op.k === 'del') {
      oi++;
    } else {
      let t = op.text;
      if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(p)) {
        t = f + t.slice(p.length);
      }
      out.push(t);
    }
  }
  return out;
}

// ---------------------------------------------------------------- tree

type TreeNow = Map<string, string | null>;

class Tree {
  now: TreeNow = new Map();
  moves: Array<{ old: string; nw: string }> = [];

  original(p: string): string | null {
    try {
      if (!fs.statSync(p).isFile()) return null;
      return fs.readFileSync(p, 'utf8');
    } catch {
      return null;
    }
  }

  get(p: string): string | null {
    if (this.now.has(p)) return this.now.get(p)!;
    return this.original(p);
  }
}

type Edit = (tree: Tree) => void;

// ---------------------------------------------------------------- detect (§4)

function detect(lines: string[]): Format {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!blank(lines[i]!)) {
      first = i;
      break;
    }
  }
  if (first < 0) return 'auto'; // error: format
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  for (const l of lines) {
    if (l.trimEnd() === '<<<<<<< SEARCH') return 'search-replace';
  }
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ '))) {
      return 'unified';
    }
  }
  return 'auto'; // error: format
}

// ---------------------------------------------------------------- unified (§6)

interface UniOp extends Op {
  noNl: boolean; // a \ line follows this op
}
interface UniHunk {
  a: number; // old start line (1-based)
  ops: UniOp[];
}
interface UniSection {
  pairOld: string | null | undefined; // undefined = no ---/+++ pair
  pairNew: string | null | undefined;
  renameOld: string | undefined;
  renameNew: string | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  isCreate: boolean;
  isDelete: boolean;
  hunks: UniHunk[];
}

function uniPath(line: string): string | null {
  // Text after the four characters, up to the first tab, surrounding spaces
  // removed. /dev/null means no file. A leading a/ or b/ is removed.
  const raw = trimSpaces(line.slice(4).split('\t')[0]!);
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

function uniResolve(sec: UniSection): { old: string | null; nw: string | null } {
  const old = sec.pairOld !== undefined ? sec.pairOld : sec.renameOld !== undefined ? sec.renameOld : (sec.diffOld ?? null);
  const nw = sec.pairNew !== undefined ? sec.pairNew : sec.renameNew !== undefined ? sec.renameNew : (sec.diffNew ?? null);
  return { old, nw };
}

// Apply hunks in order to a file's text. d = sum of (N.length - O.length)
// over hunks applied so far. Throws Fail('no-match', path) on a hunk failure.
function applyUnifiedHunks(text: string, hunks: UniHunk[], strict: boolean, p: string): string {
  const st = splitFile(text);
  let d = 0;
  for (const h of hunks) {
    const ops: Op[] = h.ops.map((o) => ({ k: o.k, text: o.text }));
    const o = ops.filter((x) => x.k !== 'add').map((x) => x.text);
    const n = ops.filter((x) => x.k !== 'del').map((x) => x.text);
    let noNlAfterLast = false;
    for (let i = h.ops.length - 1; i >= 0; i--) {
      const op = h.ops[i]!;
      if (op.k === 'ctx' || op.k === 'add') {
        noNlAfterLast = op.noNl;
        break;
      }
    }
    if (o.length > 0) {
      const found = findTier(st.lines, o, strict, 0);
      if (!found) throw new Fail('no-match', p);
      const target = h.a - 1 + d;
      let best = found.positions[0]!;
      for (const pos of found.positions) {
        if (Math.abs(pos - target) < Math.abs(best - target)) best = pos;
      }
      const atEnd = best + o.length === st.lines.length;
      const repl = applyOps(st.lines, best, ops, found.tier);
      st.lines.splice(best, o.length, ...repl);
      if (atEnd) st.final = !noNlAfterLast;
    } else {
      // Empty O: N is inserted after the first A + d lines.
      const idx = Math.max(0, Math.min(h.a + d, st.lines.length));
      const atEnd = idx === st.lines.length;
      st.lines.splice(idx, 0, ...n);
      if (atEnd) st.final = !noNlAfterLast;
    }
    d += n.length - o.length;
  }
  return joinFile(st);
}

function unifiedSectionEdit(sec: UniSection, strict: boolean): Edit {
  const { old, nw } = uniResolve(sec);
  return (tree: Tree) => {
    if (old === null || sec.isCreate) {
      // Creation: the new file is the + lines of all hunks, LF, ended by a
      // line break unless a \ line follows its last + line.
      const p = nw ?? '';
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const plus: string[] = [];
      let lastPlusNoNl = false;
      for (const h of sec.hunks) {
        for (const op of h.ops) {
          if (op.k === 'add') {
            plus.push(op.text);
            lastPlusNoNl = op.noNl;
          }
        }
      }
      tree.now.set(p, plus.length === 0 ? '' : plus.join('\n') + (lastPlusNoNl ? '' : '\n'));
      return;
    }
    if (nw === null || sec.isDelete) {
      // Deletion: the hunks are not read.
      if (!safe(old)) throw new Fail('unsafe', old);
      if (tree.get(old) === null) throw new Fail('missing', old);
      tree.now.set(old, null);
      return;
    }
    if (old !== nw) {
      // Move: hunks apply to the old file's lines, result at the new path.
      if (!safe(old)) throw new Fail('unsafe', old);
      if (!safe(nw)) throw new Fail('unsafe', nw);
      const text = tree.get(old);
      if (text === null) throw new Fail('missing', old);
      if (tree.get(nw) !== null) throw new Fail('exists', nw);
      const out = applyUnifiedHunks(text, sec.hunks, strict, old);
      tree.now.set(old, null);
      tree.now.set(nw, out);
      tree.moves.push({ old, nw });
      return;
    }
    // Change.
    if (!safe(old)) throw new Fail('unsafe', old);
    const text = tree.get(old);
    if (text === null) throw new Fail('missing', old);
    tree.now.set(old, applyUnifiedHunks(text, sec.hunks, strict, old));
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let inHeader = false;
  let hasPair = false;
  const newSection = (): UniSection => {
    const s: UniSection = {
      pairOld: undefined,
      pairNew: undefined,
      renameOld: undefined,
      renameNew: undefined,
      diffOld: undefined,
      diffNew: undefined,
      isCreate: false,
      isDelete: false,
      hunks: [],
    };
    sections.push(s);
    cur = s;
    inHeader = true;
    hasPair = false;
    return s;
  };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const s = newSection();
      s.diffOld = m[1]!;
      s.diffNew = m[2]!;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader && !hasPair) {
        cur.pairOld = uniPath(line);
        cur.pairNew = uniPath(lines[i + 1]!);
        hasPair = true;
      } else {
        const s = newSection();
        s.pairOld = uniPath(line);
        s.pairNew = uniPath(lines[i + 1]!);
        hasPair = true;
      }
      i += 2;
      continue;
    }
    if (line.startsWith('--- ') && cur !== null && inHeader) {
      // A --- line in a section's header not followed by +++.
      throw new Exit2(`error: parse ${i + 2}`);
    }
    if (line.startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (cur === null || !m) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseInt(m[1]!, 10);
      // Collect the body: lines starting with ' ', '-', '+', '\', or empty.
      // It ends at the first other line, at diff --git, or at a ---/+++ pair.
      let j = i + 1;
      while (j < lines.length) {
        const b = lines[j]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (b === '' || b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.startsWith('\\')) {
          j++;
        } else {
          break;
        }
      }
      // Trailing empty lines are not part of the body.
      let end = j;
      while (end > i + 1 && lines[end - 1] === '') end--;
      const ops: UniOp[] = [];
      for (let k = i + 1; k < end; k++) {
        const b = lines[k]!;
        if (b === '') ops.push({ k: 'ctx', text: '', noNl: false });
        else if (b.startsWith(' ')) ops.push({ k: 'ctx', text: b.slice(1), noNl: false });
        else if (b.startsWith('-')) ops.push({ k: 'del', text: b.slice(1), noNl: false });
        else if (b.startsWith('+')) ops.push({ k: 'add', text: b.slice(1), noNl: false });
        else if (b.startsWith('\\')) {
          // A \ line marks the previous body op as no-newline.
          if (ops.length > 0) ops[ops.length - 1]!.noNl = true;
        }
      }
      cur.hunks.push({ a, ops });
      inHeader = false;
      i = j;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ')) cur.renameOld = trimSpaces(line.slice('rename from '.length));
      else if (line.startsWith('rename to ')) cur.renameNew = trimSpaces(line.slice('rename to '.length));
      else if (line.startsWith('new file mode')) cur.isCreate = true;
      else if (line.startsWith('deleted file mode')) cur.isDelete = true;
      // index, old mode, new mode, similarity, dissimilarity, Index:, and
      // any other line in the header are ignored.
      i++;
      continue;
    }
    // Prose, code fences, and anything else outside a section or body.
    i++;
  }
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

// ---------------------------------------------------------------- search/replace (§7)

function srEdit(p: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree: Tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (oldLines.length === 0) {
      // Creation.
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const text = tree.get(p);
    if (text === null) throw new Fail('missing', p);
    const st = splitFile(text);
    const found = findTier(st.lines, oldLines, strict, 0);
    if (!found) throw new Fail('no-match', p);
    if (found.positions.length > 1) throw new Fail('ambiguous', p);
    const ops: Op[] = [
      ...oldLines.map((t): Op => ({ k: 'del', text: t })),
      ...newLines.map((t): Op => ({ k: 'add', text: t })),
    ];
    const repl = applyOps(st.lines, found.positions[0]!, ops, found.tier);
    st.lines.splice(found.positions[0]!, oldLines.length, ...repl);
    tree.now.set(p, joinFile(st));
  };
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevEnd = 0; // index after the previous block's REPLACE line
  let i = 0;
  while (i < lines.length) {
    let s = -1;
    for (let j = i; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s < 0) break;
    let e = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        e = j;
        break;
      }
    }
    if (e < 0) throw new Exit2(`error: parse ${s + 1}`);
    let r = -1;
    for (let j = e + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        r = j;
        break;
      }
    }
    if (r < 0) throw new Exit2(`error: parse ${s + 1}`);
    // The path is the nearest line before SEARCH, after the previous block's
    // REPLACE line, non-blank, whose trimmed form does not start with ```.
    let p: string | null = null;
    for (let j = s - 1; j >= prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      p = t;
      break;
    }
    if (p === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      p = prevPath;
    }
    edits.push(srEdit(p, lines.slice(s + 1, e), lines.slice(e + 1, r), strict));
    prevPath = p;
    prevEnd = r + 1;
    i = r + 1;
  }
  return edits;
}

// ---------------------------------------------------------------- V4A (§8)

interface V4Chunk {
  anchor: string | null; // null = no anchor
  ops: Op[];
  eof: boolean; // anchored to the end of the file
}

function v4aAddEdit(p: string, fileLines: string[]): Edit {
  return (tree: Tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (tree.get(p) !== null) throw new Fail('exists', p);
    tree.now.set(p, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
  };
}

function v4aDeleteEdit(p: string): Edit {
  return (tree: Tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (tree.get(p) === null) throw new Fail('missing', p);
    tree.now.set(p, null);
  };
}

function v4aUpdateEdit(p: string, moveTo: string | undefined, chunks: V4Chunk[], strict: boolean): Edit {
  return (tree: Tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (moveTo !== undefined && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const text = tree.get(p);
    if (text === null) throw new Fail('missing', p);
    if (moveTo !== undefined && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const st = splitFile(text);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        const at = findSingle(st.lines, ch.anchor, strict, cursor);
        if (at === null) throw new Fail('no-match', p);
        cursor = at + 1;
      }
      const o = ch.ops.filter((x) => x.k !== 'add').map((x) => x.text);
      if (o.length > 0) {
        const found = findTier(st.lines, o, strict, cursor, ch.eof);
        if (!found) throw new Fail('no-match', p);
        const pos = found.positions[0]!;
        const repl = applyOps(st.lines, pos, ch.ops, found.tier);
        st.lines.splice(pos, o.length, ...repl);
        cursor = pos + repl.length;
      } else {
        // Empty O: insert N at the cursor, or at the end for an EOF chunk.
        const idx = ch.eof ? st.lines.length : cursor;
        const n = ch.ops.filter((x) => x.k !== 'del').map((x) => x.text);
        st.lines.splice(idx, 0, ...n);
        cursor = idx + n.length;
      }
    }
    const out = joinFile(st);
    if (moveTo !== undefined) {
      tree.now.set(p, null);
      tree.now.set(moveTo, out);
      tree.moves.push({ old: p, nw: moveTo });
    } else {
      tree.now.set(p, out);
    }
  };
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') {
    throw new Exit2(`error: parse ${lines.length + 1}`);
  }
  const edits: Edit[] = [];
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');

  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const p = trimSpaces(line.slice('*** Add File: '.length));
      const raw: Array<{ l: string; no: number }> = [];
      let j = i + 1;
      while (j < last) {
        const l = lines[j]!;
        if (isSectionStart(l)) break;
        raw.push({ l, no: j + 1 });
        j++;
      }
      // Blank lines at the end of a section are not part of it.
      while (raw.length > 0 && blank(raw[raw.length - 1]!.l)) raw.pop();
      for (const { l, no } of raw) {
        if (!l.startsWith('+') && l !== '') throw new Exit2(`error: parse ${no}`);
      }
      edits.push(v4aAddEdit(p, raw.map(({ l }) => (l === '' ? '' : l.slice(1)))));
      i = j;
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const p = trimSpaces(line.slice('*** Delete File: '.length));
      let j = i + 1;
      while (j < last) {
        const l = lines[j]!;
        if (isSectionStart(l)) break;
        if (!blank(l)) throw new Exit2(`error: parse ${j + 1}`);
        j++;
      }
      edits.push(v4aDeleteEdit(p));
      i = j;
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const p = trimSpaces(line.slice('*** Update File: '.length));
      const updateLine = i + 1;
      // Collect the section's lines with their line numbers.
      const raw: Array<{ l: string; no: number }> = [];
      let j = i + 1;
      while (j < last) {
        const l = lines[j]!;
        if (isSectionStart(l)) break;
        raw.push({ l, no: j + 1 });
        j++;
      }
      while (raw.length > 0 && blank(raw[raw.length - 1]!.l)) raw.pop();
      let moveTo: string | undefined;
      let k = 0;
      if (raw.length > 0 && raw[0]!.l.startsWith('*** Move to: ')) {
        moveTo = trimSpaces(raw[0]!.l.slice('*** Move to: '.length));
        k = 1;
      }
      const chunks: V4Chunk[] = [];
      let cur: V4Chunk | null = null;
      let sawChunk = false;
      for (; k < raw.length; k++) {
        const { l, no } = raw[k]!;
        if (l.startsWith('@@')) {
          if (cur) chunks.push(cur);
          const anchor = trimSpaces(l.slice(2));
          cur = { anchor: anchor === '' ? null : anchor, ops: [], eof: false };
          sawChunk = true;
        } else if (l === '*** End of File') {
          if (cur) {
            cur.eof = true;
            chunks.push(cur);
            cur = null;
          } else {
            // An End of File line with no chunk in progress ends an empty
            // chunk anchored to the end of the file.
            chunks.push({ anchor: null, ops: [], eof: true });
            sawChunk = true;
          }
        } else if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
          if (!cur) {
            // Only the first chunk may start at a body line.
            if (sawChunk) throw new Exit2(`error: parse ${no}`);
            cur = { anchor: null, ops: [], eof: false };
            sawChunk = true;
          }
          if (l === '') cur.ops.push({ k: 'ctx', text: '' });
          else if (l.startsWith(' ')) cur.ops.push({ k: 'ctx', text: l.slice(1) });
          else if (l.startsWith('-')) cur.ops.push({ k: 'del', text: l.slice(1) });
          else cur.ops.push({ k: 'add', text: l.slice(1) });
        } else {
          throw new Exit2(`error: parse ${no}`);
        }
      }
      if (cur) chunks.push(cur);
      if (chunks.length === 0 && moveTo === undefined) {
        throw new Exit2(`error: parse ${updateLine}`);
      }
      edits.push(v4aUpdateEdit(p, moveTo, chunks, strict));
      i = j;
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  return edits;
}

// ---------------------------------------------------------------- JSON (§9)

interface JsonEditSpec {
  path: string;
  command: 'create' | 'str_replace' | 'insert';
  file_text?: string;
  old_str?: string;
  new_str?: string;
  insert_line?: number;
}

// An edit object has a string `path` and a `command`; keys other than those
// below are ignored. A wrong command or a missing or mistyped key is a parse
// fault. Returns null on a fault.
function validateJsonEdit(obj: unknown): JsonEditSpec | null {
  if (typeof obj !== 'object' || obj === null || Array.isArray(obj)) return null;
  const o = obj as Record<string, unknown>;
  if (typeof o.path !== 'string') return null;
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    return { path: o.path, command: 'create', file_text: o.file_text };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') return null;
    if (o.new_str === undefined) {
      return { path: o.path, command: 'str_replace', old_str: o.old_str, new_str: '' };
    }
    if (typeof o.new_str !== 'string') return null;
    return { path: o.path, command: 'str_replace', old_str: o.old_str, new_str: o.new_str };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== 'string') return null;
    return { path: o.path, command: 'insert', insert_line: o.insert_line, new_str: o.new_str };
  }
  return null;
}

function jsonEdit(spec: JsonEditSpec): Edit {
  return (tree: Tree) => {
    const p = spec.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (spec.command === 'create') {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, spec.file_text!);
      return;
    }
    if (spec.command === 'str_replace') {
      const text = tree.get(p);
      if (text === null) throw new Fail('missing', p);
      // In a CRLF file, the file's text and both strings are read with every
      // \r\n as \n, and the result is written back with \r\n. No tier
      // applies: the match is exact.
      const isCRLF = splitFile(text).br === '\r\n';
      const hay = isCRLF ? text.replace(/\r\n/g, '\n') : text;
      const oldStr = isCRLF ? spec.old_str!.replace(/\r\n/g, '\n') : spec.old_str!;
      const newStr = isCRLF ? spec.new_str!.replace(/\r\n/g, '\n') : spec.new_str!;
      let count = 0;
      let firstIdx = -1;
      let idx = 0;
      while (count < 2) {
        const at = hay.indexOf(oldStr, idx);
        if (at < 0) break;
        if (firstIdx < 0) firstIdx = at;
        count++;
        idx = at + 1; // positions may overlap
      }
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const replaced = hay.slice(0, firstIdx) + newStr + hay.slice(firstIdx + oldStr.length);
      tree.now.set(p, isCRLF ? replaced.replace(/\n/g, '\r\n') : replaced);
      return;
    }
    // insert: insert_line from 0 to the file's number of lines (else
    // no-match); new_str's lines are inserted after line insert_line.
    const text = tree.get(p);
    if (text === null) throw new Fail('missing', p);
    const st = splitFile(text);
    const at = spec.insert_line!;
    if (at < 0 || at > st.lines.length) throw new Fail('no-match', p);
    st.lines.splice(at, 0, ...patchLines(spec.new_str!));
    tree.now.set(p, joinFile(st));
  };
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!blank(lines[i]!)) {
      first = i;
      break;
    }
  }
  if (first < 0) return [];
  if (lines[first]!.trimStart()[0] === '[') {
    // Array form: any fault is parse at the line where the array starts.
    const startLine = first + 1;
    let parsed: unknown;
    try {
      parsed = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${startLine}`);
    }
    if (!Array.isArray(parsed)) throw new Exit2(`error: parse ${startLine}`);
    const edits: Edit[] = [];
    for (const obj of parsed) {
      const spec = validateJsonEdit(obj);
      if (!spec) throw new Exit2(`error: parse ${startLine}`);
      edits.push(jsonEdit(spec));
    }
    return edits;
  }
  // JSON Lines form: a line that does not hold one valid edit object is
  // parse at that line; blank lines are ignored.
  const edits: Edit[] = [];
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!;
    if (blank(l)) continue;
    let obj: unknown;
    try {
      obj = JSON.parse(l);
    } catch {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const spec = validateJsonEdit(obj);
    if (!spec) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(jsonEdit(spec));
  }
  return edits;
}

// ---------------------------------------------------------------- run

function run(args: string[], cwd: string): { code: number; out: string } {
  let check = false;
  let strict = false;
  let format: Format | null = null;
  let file: string | null = null;
  let seenDashDash = false;
  let optionTwice: string | null = null;
  const seenOptions = new Set<string>();
  for (const a of args) {
    if (seenDashDash) {
      if (file !== null) return { code: 2, out: 'error: usage\n' };
      file = a;
      continue;
    }
    if (a === '--') {
      seenDashDash = true;
      continue;
    }
    if (a === '--check') {
      if (seenOptions.has('--check')) optionTwice = '--check';
      seenOptions.add('--check');
      check = true;
      continue;
    }
    if (a === '--strict') {
      if (seenOptions.has('--strict')) optionTwice = '--strict';
      seenOptions.add('--strict');
      strict = true;
      continue;
    }
    if (a.startsWith('--format=')) {
      if (seenOptions.has('--format')) optionTwice = '--format';
      seenOptions.add('--format');
      const v = a.slice('--format='.length);
      if (!(FORMATS as readonly string[]).includes(v)) {
        return { code: 2, out: 'error: usage\n' };
      }
      format = v as Format;
      continue;
    }
    if (a.startsWith('--')) {
      return { code: 2, out: 'error: usage\n' };
    }
    if (a.startsWith('-') && a !== '-') {
      return { code: 2, out: 'error: usage\n' };
    }
    if (file !== null) return { code: 2, out: 'error: usage\n' };
    file = a;
  }
  if (optionTwice) return { code: 2, out: `error: usage ${optionTwice}\n` };

  let text: string;
  if (file !== null && file !== '-') {
    try {
      text = fs.readFileSync(path.resolve(cwd, file), 'utf8');
    } catch {
      return { code: 2, out: 'error: no-patch\n' };
    }
  } else {
    try {
      text = fs.readFileSync(0, 'utf8');
    } catch {
      return { code: 2, out: 'error: usage\n' };
    }
  }

  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === 'auto') return { code: 2, out: 'error: format\n' };

  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: e.message + '\n' };
    throw e;
  }

  const tree = new Tree();
  const fails: Array<{ kind: string; p: string }> = [];
  for (const e of edits) {
    const snap = new Map(tree.now);
    try {
      e(tree);
    } catch (err) {
      tree.now = snap;
      if (err instanceof Fail) fails.push({ kind: err.kind, p: err.p });
      else throw err;
    }
  }
  if (fails.length > 0) {
    const out: string[] = [];
    for (const f of fails) out.push(`error: ${f.kind} ${f.p}`);
    out.push(`failed: ${fails.length} of ${edits.length} edits`);
    return { code: 1, out: out.join('\n') + '\n' };
  }

  // Changed paths: tree.now differs from the original.
  const changed: string[] = [];
  for (const p of tree.now.keys()) {
    if (tree.original(p) !== tree.now.get(p)) changed.push(p);
  }

  // Move lines: R old -> new when old existed before the patch and does not
  // after it, and new did not exist before it and does after it. R replaces
  // that pair's D and A lines, and sorts by <new>.
  const rows: Array<{ key: string; line: string }> = [];
  const suppressed = new Set<string>();
  const seenR = new Set<string>();
  for (const mv of tree.moves) {
    const key = mv.old + '\u0000' + mv.nw;
    if (seenR.has(key)) continue;
    seenR.add(key);
    if (tree.original(mv.old) !== null && tree.get(mv.old) === null && tree.original(mv.nw) === null && tree.get(mv.nw) !== null) {
      rows.push({ key: mv.nw, line: `R ${mv.old} -> ${mv.nw}` });
      suppressed.add(mv.old);
      suppressed.add(mv.nw);
    }
  }
  for (const p of changed) {
    if (suppressed.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));

  if (!check) {
    for (const p of changed) {
      const now = tree.now.get(p)!;
      if (now === null) {
        fs.rmSync(p, { force: true });
      } else {
        fs.mkdirSync(path.dirname(p), { recursive: true });
        fs.writeFileSync(p, now);
      }
    }
  }
  const out: string[] = rows.map((r) => r.line);
  out.push(`ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`);
  return { code: 0, out: out.join('\n') + '\n' };
}

// ---------------------------------------------------------------- main (kit hand-over, unchanged)

function trialMain(argv: string[], cwd: string): { code: number; out: string } {
  const args = argv.filter((a) => !a.startsWith('--trial') && !a.startsWith('--workdir'));
  return run(args, cwd);
}

function envMain(argv: string[]): { code: number; out: string } {
  const outPath = process.env.MAKEFUN_ENV_URL;
  const result = trialMain(argv, process.cwd());
  if (outPath !== undefined && outPath !== '') {
    try {
      const parsed = new URL(outPath);
      if (parsed.protocol === 'file:') {
        const target = fileURLToPath(parsed);
        fs.writeFileSync(target, JSON.stringify({ code: result.code, stdout: result.out }));
      }
    } catch {
      // env hand-over is best-effort
    }
  }
  return result;
}

function isMain(): boolean {
  const mainPath = process.argv[1];
  if (!mainPath) return false;
  const here = fileURLToPath(import.meta.url);
  return path.resolve(mainPath) === path.resolve(here);
}

if (isMain()) {
  const url = process.env.MAKEFUN_ENV_URL;
  if (url !== undefined && url !== '') {
    try {
      const parsed = new URL(url);
      if (parsed.protocol === 'file:') {
        envMain(process.argv.slice(2));
        process.exit(0);
      }
    } catch {
      // fall through to normal main
    }
  }
  const out = run(process.argv.slice(2), process.cwd());
  process.stdout.write(out.out);
  process.exit(out.code);
}

export { run, trialMain };
