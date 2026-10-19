-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_factorial_succ
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:16:46.684707+00:00
-- url     : https://prove2.me/theorems/c465c227-93e2-4e19-a23a-7add0ee580ca
-- title:
--   Unit simplex volume recurrence
-- statement:
--   In dimension `n + 1`, slicing by one coordinate and integrating the volumes of the scaled `n`-simplex sections gives the `n`-dimensional simplex volume divided by `n + 1`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial_succ (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal / (n + 1 : ℝ) := by sorry
