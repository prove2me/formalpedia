-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_real_integral_eval
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_real_integral_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:45:17.835609+00:00
-- url     : https://prove2.me/theorems/04b9904e-e789-4020-9de6-34d1db97c9e6
-- title:
--   Evaluate the real supported scaled-slice integral
-- statement:
--   For every natural number n, the real integral of the power function supported on the unit interval is the reciprocal of n + 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_real_integral_eval (n : ℕ) :
    ∫ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then (1 - t) ^ n else 0)
      ∂MeasureTheory.volume = (((n : ℝ) + 1)⁻¹) := by sorry
