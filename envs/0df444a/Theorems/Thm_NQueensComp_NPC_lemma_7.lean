-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_7
-- name    : NQueensComp.NPC.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:32.995271+00:00
-- url     : https://prove2.me/theorems/9b4a3c84-1c63-428a-85f5-db16e58eb8f1
-- title:
--   Lemma 7 — Aₙ and Bₙ are modular solutions with the same diagonals for n ≡ 1, 5 (mod 6)
-- statement:
--   **Lemma 7.** If $n\equiv1\pmod 6$ or $n\equiv5\pmod 6$, then $A_n=\{(i,2i\bmod n)\}$ and $B_n=\{(2i\bmod n,i)\}$ are modular solutions to the $n$-Queens problem, and
--   $$\{\alpha+\beta\mid(\alpha,\beta)\in A_n\}=\{\alpha+\beta\mid(\alpha,\beta)\in B_n\},\qquad\{\alpha-\beta\mid(\alpha,\beta)\in A_n\}=\{\alpha-\beta\mid(\alpha,\beta)\in B_n\}.$$
--
--   The first part is due to Bell and Stevens (2009, Thm. 9). The second part is what lets Definition 10 swap one copy of $A_{n'}$ for $B_{n'}$ via Lemma 8.
--
--   Differences from the source:
--   - reading: “use the same sets of sum-/difference-diagonals as each other” → equal sets of the integers α + β, and equal sets of the integers α − β; reason: the proof computes the integer values, not residues mod n
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 823, Lemma 7

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Lemma 7, p. 823: if `n ≡ 1 (mod 6)` or `n ≡ 5 (mod 6)` then `Aₙ` and `Bₙ` are modular
solutions to the `n`-Queens problem, and they use the same set of sum-diagonals and the same set of
difference-diagonals. -/
theorem lemma_7 (n : ℕ) (hn : n % 6 = 1 ∨ n % 6 = 5) :
    IsModularSol n (A n) ∧ IsModularSol n (B n) ∧
      (A n).image sumDiag = (B n).image sumDiag ∧
      (A n).image diffDiag = (B n).image diffDiag := by sorry

end NQueensComp.NPC
