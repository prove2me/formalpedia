-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_9
-- name    : NQueensComp.NPC.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:24.675985+00:00
-- url     : https://prove2.me/theorems/1ead809a-e442-4162-bb2f-21e60845daf2
-- title:
--   Lemma 9 — n-scaled queens whose offsets differ enough do not attack
-- statement:
--   Let $n\ge1$, let $q_1,q_2$ be queens that fit on board size $n$, and let $q_3,q_4$ be queens of any size.
--
--   **Lemma 9.**
--   1. If $\mathrm{col}(q_3)\ne\mathrm{col}(q_4)$, then $\mathrm{col}(q_1+nq_3)\ne\mathrm{col}(q_2+nq_4)$.
--   2. If $\mathrm{row}(q_3)\ne\mathrm{row}(q_4)$, then $\mathrm{row}(q_1+nq_3)\ne\mathrm{row}(q_2+nq_4)$.
--   3. If the sum-diagonals of $q_3,q_4$ differ by more than one, then the sum-diagonals of $q_1+nq_3$ and $q_2+nq_4$ differ.
--   4. If the difference-diagonals of $q_3,q_4$ differ by more than one, then the difference-diagonals of $q_1+nq_3$ and $q_2+nq_4$ differ.
--   5. If all four hypotheses hold, then $q_1+nq_3$ does not attack $q_2+nq_4$:
--   $$\mathrm{col}\ne,\ \mathrm{row}\ne,\ |\Sigma_3-\Sigma_4|>1,\ |\Delta_3-\Delta_4|>1\ \Longrightarrow\ q_1+nq_3 \text{ does not attack } q_2+nq_4,$$
--   where $\Sigma$ and $\Delta$ denote sum- and difference-diagonals.
--
--   This is the basic tool for embedding sub-boards of size $n$ into a coarser grid without interference (Definitions 10 and 20).
--
--   Differences from the source: none.
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 824, Lemma 9

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Lemma 9, p. 824: let `q₁, q₂` fit on board size `n` and let `q₃, q₄` be any queens.  If the
columns (rows) of `q₃, q₄` differ, so do the columns (rows) of `q₁ + nq₃` and `q₂ + nq₄`; if the
sum-diagonals (difference-diagonals) of `q₃, q₄` differ by more than one, then the sum-diagonals
(difference-diagonals) of `q₁ + nq₃` and `q₂ + nq₄` differ; if all four hold, `q₁ + nq₃` does not
attack `q₂ + nq₄`. -/
theorem lemma_9 (n : ℕ) (q₁ q₂ q₃ q₄ : Queen) (h₁ : FitsOn n q₁) (h₂ : FitsOn n q₂) :
    (col q₃ ≠ col q₄ → col (q₁ + n • q₃) ≠ col (q₂ + n • q₄)) ∧
    (row q₃ ≠ row q₄ → row (q₁ + n • q₃) ≠ row (q₂ + n • q₄)) ∧
    (1 < |((sumDiag q₃ : ℕ) : ℤ) - ((sumDiag q₄ : ℕ) : ℤ)| →
      sumDiag (q₁ + n • q₃) ≠ sumDiag (q₂ + n • q₄)) ∧
    (1 < |diffDiag q₃ - diffDiag q₄| → diffDiag (q₁ + n • q₃) ≠ diffDiag (q₂ + n • q₄)) ∧
    (col q₃ ≠ col q₄ → row q₃ ≠ row q₄ →
      1 < |((sumDiag q₃ : ℕ) : ℤ) - ((sumDiag q₄ : ℕ) : ℤ)| →
      1 < |diffDiag q₃ - diffDiag q₄| → ¬ Attacks (q₁ + n • q₃) (q₂ + n • q₄)) := by sorry

end NQueensComp.NPC
