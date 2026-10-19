-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_nonnegative_dilation
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_nonnegative_dilation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:43:55.305886+00:00
-- url     : https://prove2.me/theorems/2cb8f0c2-bc38-41d3-a7d5-83f030c0725f
-- title:
--   Volume scaling of nonnegative simplexes
-- statement:
--   For every nonnegative radius r, the dimension-n simplex volume is r^n times the unit simplex volume, including zero radius and dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_nonnegative_dilation
    (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ r}) =
    r ^ n * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by sorry
