-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_row_card_pos
-- name    : OAI.PiExponent.MatrixArithmetic.selectedMinor_row_card_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:21:11.762509+00:00
-- url     : https://prove2.me/theorems/89673420-fb74-4e19-9bfc-2aa1302ecb02
-- title:
--   Positive cardinality of the interpolation row domain
-- statement:
--   For positive `K` and `H`, the interpolation row domain contains a row formed from any first coordinate in `Fin K` and the zero multi-index, so its finite cardinality is positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_row_card_pos
    {m K : ℕ} {v0 θ H : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H) :
    0 < (Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) := by sorry
