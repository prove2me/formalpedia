-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:21:43.859782+00:00
-- url     : https://prove2.me/theorems/98402f01-9a77-402a-9af4-d8616b6ef95a
-- title:
--   Simplex volume slice recurrence
-- statement:
--   The unit nonnegative simplex in m+1 coordinates has volume equal to the m-dimensional unit simplex volume divided by m+1. The recurrence also covers m=0, where both volumes are 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_succ (m : ℕ) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ 1}).toReal =
      ((MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1}).toReal) / (m + 1 : ℝ) := by sorry
