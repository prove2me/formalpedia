-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume
-- name    : OAI.PiExponent.DeterminantContradiction.unit_simplex_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:47:01.479353+00:00
-- url     : https://prove2.me/theorems/18cd962e-7034-4515-9328-f633744c24ce
-- title:
--   Volume of the unit nonnegative simplex
-- statement:
--   The unit nonnegative simplex in dimension k has volume the reciprocal of k factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.unit_simplex_volume (k : ℕ) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal =
      (Nat.factorial k : ℝ)⁻¹ := by sorry
