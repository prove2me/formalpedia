-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_positive_dilation
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_positive_dilation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:57:23.072665+00:00
-- url     : https://prove2.me/theorems/8eadaa24-aac7-46bc-ac7d-94b369ae7dfb
-- title:
--   Positive-radius simplex volume scaling
-- statement:
--   For positive radius, dilation by that radius scales the volume of the nonnegative simplex by the radius to the dimension.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_positive_dilation
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ r}) =
    r ^ n * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by sorry
