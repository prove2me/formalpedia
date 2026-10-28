-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_8
-- name    : NQueensComp.NPC.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:29.325581+00:00
-- url     : https://prove2.me/theorems/d7c9afe7-10c7-4b9a-ace2-18df707011aa
-- title:
--   Lemma 8 (Rivin–Zabih) — exchanging a subset for one with the same lines (corrected: |P₁| = |P| added)
-- statement:
--   **Lemma 8 (Rivin and Zabih), corrected.** Let $Q$ be a solution to the $n$-Queens problem and $P\subseteq Q$. If $P_1$ is a set of queens with $|P_1|=|P|$ that uses the same set of rows, the same set of columns, the same set of sum-diagonals and the same set of difference-diagonals as $P$, then
--   $$(Q\setminus P)\cup P_1$$
--   is also a solution to the $n$-Queens problem.
--
--   Definition 10 uses it to replace the copy $A_{n'}+n'(17,0)$ by $B_{n'}+n'(17,0)$ in Lemma 12.
--
--   Differences from the source:
--   - correction: Lemma 8 has no hypothesis on the size of P₁ → adds |P₁| = |P|; reason: false as printed: n = 4, Q = P = {(1,0), (3,1), (0,2), (2,3)} and P₁ = Q ∪ {(2,0), (0,1), (3,2), (1,3)} use the same rows, columns, sum-diagonals {1, 2, 4, 5} and difference-diagonals {−2, −1, 1, 2}, but (Q \ P) ∪ P₁ has 8 queens; the paper's use (Lemma 12) has |P₁| = |P| = n′
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 823, Lemma 8 (Rivin & Zabih 1992, Thm. 2.4)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Lemma 8 (Rivin and Zabih), p. 823, corrected: if `Q` is a solution to the `n`-Queens
problem, `P ⊆ Q`, and `P₁` is a set of queens with `|P₁| = |P|` (added; the printed lemma is false
without it) that uses the same sets of rows, columns, sum-diagonals and difference-diagonals as `P`,
then `(Q \ P) ∪ P₁` is a solution to the `n`-Queens problem. -/
theorem lemma_8 (n : ℕ) (Q P P₁ : Finset Queen) (hQ : IsNQueensSol n Q) (hPQ : P ⊆ Q)
    (hcard : P₁.card = P.card)
    (hrow : P₁.image row = P.image row) (hcol : P₁.image col = P.image col)
    (hsum : P₁.image sumDiag = P.image sumDiag) (hdiff : P₁.image diffDiag = P.image diffDiag) :
    IsNQueensSol n ((Q \ P) ∪ P₁) := by sorry

end NQueensComp.NPC
