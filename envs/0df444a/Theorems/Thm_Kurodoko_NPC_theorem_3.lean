-- Prove2me | Theorems.Thm_Kurodoko_NPC_theorem_3
-- name    : Kurodoko.NPC.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:56.349754+00:00
-- url     : https://prove2.me/theorems/bde0c770-073c-479a-8680-cc4c427d1e32
-- title:
--   Theorem 3, p. 695 — the Kurodoko Decision Problem is NP-hard (given that one-in-three SAT is NP-complete)
-- statement:
--   **Theorem 3.** The Kurodoko Decision Problem is NP-hard.
--
--   Assume that one-in-three SAT is NP-complete (Schaefer 1978, cited in §3). Then every language $L'$ in $\mathbf{NP}$, over any finite nonempty alphabet, reduces to Kurodoko:
--   $$L'\le_p\mathsf{Kurodoko}.$$
--
--   This is the hardness half of the NP-completeness of Kurodoko.
--
--   **Formalization Note** $\mathbf{NP}$, $\le_p$ and NP-completeness are those of the published `CookPvsNP_defs`.
--
--   Differences from the source:
--   - reading: one-in-three-SAT "was shown to be NP-complete in Ref. [5]" (§3, p. 695), cited without proof → explicit hypothesis `NPComplete oneInThreeLang`; reason: the paper imports this fact from Schaefer (1978); the platform has no proof of it in the CookPvsNP framework
--   - reading: "a SAT instance", the one-in-three-SAT of Ref. [5] → a CNF whose clauses all have exactly three literals (negations and repeated variables allowed); "exactly one true" counts literal occurrences; reason: §3 reduces from one-in-three-SAT of [5]; the routing of Appendix A.1 only lines up when every clause has three literals; the reduction has one wire per occurrence
--   - encoding: w and h in binary, C as a list of points and N as a list of integers (p. 694) → code = encNats [w, h, r₁, c₁, n₁, r₂, c₂, n₂, …] (binary, clue triples interleaved), over the alphabet BSym; reason: a polynomial-time-equivalent layout of the same data; w and h stay binary
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: rule (4): ∀(r, c) ∈ V : N(r, c) = hz + vt − 1, hz with the run {(r, b + i)}_{i=0}^{k} → for every clue (r, c, n): n = touchCount (the squares of its row and column reachable through white squares, itself once); reason: N is defined only on C, and a run of length k has the squares i = 0, …, k − 1; touchCount = hz + vt − 1 for a white clue square
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 695 (PDF 2), Theorem 3; §3 and the reference [5]

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 3, p. 695, relative to the NP-completeness of one-in-three SAT (Schaefer 1978, cited
in §3): the Kurodoko Decision Problem is NP-hard. -/
theorem theorem_3 (h3 : NPComplete oneInThreeLang) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'),
      L' ∈ NP Sym' → PolyReducible L' kurodokoLang := by sorry

end Kurodoko.NPC
