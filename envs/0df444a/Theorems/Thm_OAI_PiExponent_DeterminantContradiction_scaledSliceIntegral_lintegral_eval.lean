-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_lintegral_eval
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:37:49.295608+00:00
-- url     : https://prove2.me/theorems/7967d6fe-3590-48ba-883e-fdadcf513b79
-- title:
--   Evaluate the supported scaled-slice lintegral
-- statement:
--   The ENNReal lintegral of the scaled-slice function supported on the unit interval equals the reciprocal of n + 1, embedded into ENNReal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_eval (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume =
      ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by sorry
