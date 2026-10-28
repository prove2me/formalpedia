-- Prove2me | Theorems.Thm_Kurodoko_NPC_compress_preconnected_iff
-- name    : Kurodoko.NPC.compress_preconnected_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:44.473802+00:00
-- url     : https://prove2.me/theorems/ed6963ce-f720-43bc-99ca-df09bc3ef179
-- title:
--   Proof of Theorem 2, p. 695 — merging adjacent black-free rows or columns preserves rule 3; afterwards w, h ≤ 2|B| + 1
-- statement:
--   Let $B$ be a set of squares of the board with $w$ columns and $h$ rows.
--
--   1. If rows $r$ and $r+1$ ($r+1<h$) contain no square of $B$, then the white squares are connected on the $w\times h$ board if and only if they are connected on the $w\times(h-1)$ board obtained by merging the two rows, i.e. with $B$ replaced by
--   $$B'=\{(r',c)\in B : r'\le r\}\cup\{(r'-1,c) : (r',c)\in B,\ r'>r\}.$$
--   2. The same holds for two adjacent columns $c,c+1$ without black squares, merged into one ($w-1$ columns).
--   3. If every two adjacent rows contain a black square, then $h\le 2|B|+1$; if every two adjacent columns contain one, then $w\le 2|B|+1$.
--
--   This is the compression step of the NP-membership proof: since $w$ and $h$ are given in binary, the board can be exponentially large, and compression makes the connectivity check of rule 3 run on a board of polynomial size.
--
--   Differences from the source:
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
--   - encoding: "merging adjacent rows that don't contain any black squares" → rows r, r + 1 without black squares become one row: height h − 1, every black square below row r moves up by one (columns alike); reason: a merge is the deletion of one of two identical white rows
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: "Then w, h ≤ 2 |B|+1" after merging all adjacent black-free rows and columns → if no two adjacent rows are free of black squares then h ≤ 2|B| + 1, and the same for columns and w; reason: this is the property of the fully compressed grid the sentence asserts
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 695 (PDF 2), proof of Theorem 2: "To check rule 3 if w > 2 |B| + 1 or h > 2 |B| + 1, compress the grid …"

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Proof of Theorem 2, p. 695: the compression step for rule 3. For a set `B` of squares of the
board of width `w` and height `h`:
* if rows `r` and `r + 1` contain no black square, the white squares are connected iff they are
  connected on the board with the two rows merged (height `h − 1`, rows below `r` shifted up);
* the same for two adjacent columns `c`, `c + 1` (width `w − 1`);
* if no two adjacent rows are free of black squares then `h ≤ 2|B| + 1`, and likewise
  `w ≤ 2|B| + 1` for columns. -/
theorem compress_preconnected_iff (w h : ℕ) (B : Finset Cell) (hB : ∀ v ∈ B, OnBoard w h v) :
    (∀ r, r + 1 < h → (∀ v ∈ B, v.1 ≠ r ∧ v.1 ≠ r + 1) →
      (Rule3 w h B ↔
        Rule3 w (h - 1) (B.image fun v => if r < v.1 then (v.1 - 1, v.2) else v))) ∧
    (∀ c, c + 1 < w → (∀ v ∈ B, v.2 ≠ c ∧ v.2 ≠ c + 1) →
      (Rule3 w h B ↔
        Rule3 (w - 1) h (B.image fun v => if c < v.2 then (v.1, v.2 - 1) else v))) ∧
    ((∀ r, r + 1 < h → ∃ v ∈ B, v.1 = r ∨ v.1 = r + 1) → h ≤ 2 * B.card + 1) ∧
    ((∀ c, c + 1 < w → ∃ v ∈ B, v.2 = c ∨ v.2 = c + 1) → w ≤ 2 * B.card + 1) := by sorry

end Kurodoko.NPC
