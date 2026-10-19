-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_radius
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_radius
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:57:34.953904+00:00
-- url     : https://prove2.me/theorems/e0c1df12-5f0c-4edc-bbe5-ac24cc17f7c4
-- title:
--   Zero-radius simplex volume
-- statement:
--   At radius zero, the simplex volume equals zero to the dimension times the unit simplex volume, including dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_radius
    (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (0 : ℝ)}) =
    (0 : ℝ) ^ n * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by sorry
