-- Prove2me | Theorems.Thm_Kurodoko_NPC_kurodoko_npComplete
-- name    : Kurodoko.NPC.kurodoko_npComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:56.376164+00:00
-- url     : https://prove2.me/theorems/d09061a5-c33c-4913-8bed-f5d1c7298b59
-- title:
--   Abstract and §1, p. 694 (Theorems 2 and 3, p. 695) — the Kurodoko Decision Problem is NP-complete (given that one-in-three SAT is)
-- statement:
--   The Kurodoko Decision Problem asks, for a board of width $w$ and height $h$ (given in binary) with clues $N:C\to\{1,\dots,w+h-1\}$, whether some set $B$ of black squares satisfies the four rules: clue squares are white; no two black squares are adjacent; the white squares are connected; every clue equals the number of squares it touches.
--
--   Assume that one-in-three SAT is NP-complete (Schaefer 1978, cited in §3). Then
--   $$\mathsf{Kurodoko}\ \text{is NP-complete},$$
--   that is, it is in $\mathbf{NP}$ and every language in $\mathbf{NP}$ reduces to it in polynomial time.
--
--   This is the main result of the paper: "We show that deciding the solvability of Kurodoko puzzles is NP-complete."
--
--   **Formalization Note** NP-completeness is the published `CookPvsNP.NPComplete`. The only imported fact, the NP-completeness of one-in-three SAT, is the hypothesis.
--
--   Differences from the source:
--   - reading: one-in-three-SAT "was shown to be NP-complete in Ref. [5]" (§3, p. 695), cited without proof → explicit hypothesis `NPComplete oneInThreeLang`; reason: the paper imports this fact from Schaefer (1978); the platform has no proof of it in the CookPvsNP framework
--   - reading: "a SAT instance", the one-in-three-SAT of Ref. [5] → a CNF whose clauses all have exactly three literals (negations and repeated variables allowed); "exactly one true" counts literal occurrences; reason: §3 reduces from one-in-three-SAT of [5]; the routing of Appendix A.1 only lines up when every clause has three literals; the reduction has one wire per occurrence
--   - encoding: w and h in binary, C as a list of points and N as a list of integers (p. 694) → code = encNats [w, h, r₁, c₁, n₁, r₂, c₂, n₂, …] (binary, clue triples interleaved), over the alphabet BSym; reason: a polynomial-time-equivalent layout of the same data; w and h stay binary
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: rule (4): ∀(r, c) ∈ V : N(r, c) = hz + vt − 1, hz with the run {(r, b + i)}_{i=0}^{k} → for every clue (r, c, n): n = touchCount (the squares of its row and column reachable through white squares, itself once); reason: N is defined only on C, and a run of length k has the squares i = 0, …, k − 1; touchCount = hz + vt − 1 for a white clue square
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 694 (PDF 1), abstract and §1; Theorems 2 and 3, p. 695 (PDF 2)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Abstract and §1, p. 694 (Theorems 2 and 3, p. 695), relative to the NP-completeness of
one-in-three SAT (Schaefer 1978, cited in §3): the Kurodoko Decision Problem is NP-complete. -/
theorem kurodoko_npComplete (h3 : NPComplete oneInThreeLang) : NPComplete kurodokoLang := by sorry

end Kurodoko.NPC
