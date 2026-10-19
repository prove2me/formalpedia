-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_coordinate_slicing
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:43:44.362584+00:00
-- url     : https://prove2.me/theorems/8b4cf080-e694-4a88-af59-4c98a0f6f938
-- title:
--   Simplex volume by coordinate sections
-- statement:
--   The unit simplex volume in dimension n+1 equals the integral, from zero to one, of the dimension-n simplex volumes with radius 1−t.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ∫ t in (0 : ℝ)..1, ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1 - t}) := by sorry
