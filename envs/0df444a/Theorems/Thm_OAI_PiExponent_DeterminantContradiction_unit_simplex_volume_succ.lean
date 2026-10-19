-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T20:21:39.970327+00:00
-- url     : https://prove2.me/theorems/ad9331c1-ad33-407b-be4a-2e146dc37eb4
-- title:
--   Dimension recurrence for unit simplex volume
-- statement:
--   The volume of the nonnegative unit simplex in dimension k+1 equals its dimension-k volume divided by k+1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_succ (k : ℕ) :
    (MeasureTheory.volume
      {x : Fin (k + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (k + 1), x i ≤ 1}).toReal =
      ((MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal) /
        ((k + 1 : ℕ) : ℝ) := by sorry
