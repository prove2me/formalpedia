-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_eval
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:17:37.573472+00:00
-- url     : https://prove2.me/theorems/042736fa-5ef5-4160-91c8-8dee5c2ef56b
-- title:
--   Evaluation of the scaled-slice integral
-- statement:
--   Evaluate the lintegral over the unit interval of the n-th power of the remaining slice scale as 1/(n+1), expressed in ENNReal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eval (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by sorry
