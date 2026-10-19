-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_coordinate_slicing_general
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing_general
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:55:59.524929+00:00
-- url     : https://prove2.me/theorems/6f2b1fd4-03ea-433e-8f5a-bdd3e044e160
-- title:
--   Simplex volume by coordinate sections at arbitrary radius
-- statement:
--   For every dimension and nonnegative radius, the volume of the simplex of nonnegative coordinates whose sum is at most that radius equals the integral of its coordinate-section volumes, where the remaining radius at coordinate value t is R−t.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing_general (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ R}) =
    ∫ t in (0 : ℝ)..R, ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ R - t}) := by sorry
