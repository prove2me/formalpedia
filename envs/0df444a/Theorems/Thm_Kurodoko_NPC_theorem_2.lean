-- Prove2me | Theorems.Thm_Kurodoko_NPC_theorem_2
-- name    : Kurodoko.NPC.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:47.038686+00:00
-- url     : https://prove2.me/theorems/03fbd24e-b120-459f-b56a-a951848858bf
-- title:
--   Theorem 2, p. 695 — the Kurodoko Decision Problem is in NP
-- statement:
--   **Theorem 2.** The Kurodoko Decision Problem is in NP.
--
--   The Kurodoko language consists of the binary codes of the well-formed instances $(w,h,C,N)$ that have a solution $B$ (rules 1–4). The statement is
--   $$\mathsf{Kurodoko}\in\mathbf{NP},$$
--   with $w$ and $h$ written in binary, so the board can have exponentially many squares in the length of the code.
--
--   This is the membership half of the NP-completeness of Kurodoko.
--
--   **Formalization Note** $\mathbf{NP}$ is the published `CookPvsNP.NP`: a polynomial-time checking relation (one-tape Turing machines) with witnesses of polynomial length.
--
--   Differences from the source:
--   - encoding: w and h in binary, C as a list of points and N as a list of integers (p. 694) → code = encNats [w, h, r₁, c₁, n₁, r₂, c₂, n₂, …] (binary, clue triples interleaved), over the alphabet BSym; reason: a polynomial-time-equivalent layout of the same data; w and h stay binary
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: rule (4): ∀(r, c) ∈ V : N(r, c) = hz + vt − 1, hz with the run {(r, b + i)}_{i=0}^{k} → for every clue (r, c, n): n = touchCount (the squares of its row and column reachable through white squares, itself once); reason: N is defined only on C, and a run of length k has the squares i = 0, …, k − 1; touchCount = hz + vt − 1 for a white clue square
--   - encoding: "in NP": a polynomial-time witness-checking algorithm → kurodokoLang ∈ CookPvsNP.NP BSym (one-tape Turing machines, polynomial checking relation and witness length); reason: the published complexity layer of the platform
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 695 (PDF 2), Theorem 2 and its proof

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 2, p. 695: the Kurodoko Decision Problem is in NP. -/
theorem theorem_2 : kurodokoLang ∈ NP BSym := by sorry

end Kurodoko.NPC
