-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_intervalBridge
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_intervalBridge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:24:43.516626+00:00
-- url     : https://prove2.me/theorems/f9d31c8c-3749-4436-9488-67a9cbdf68be
-- title:
--   Convert the scaled-slice lintegral to a real interval integral
-- statement:
--   Convert the ENNReal lintegral supported on the closed unit interval into the corresponding real interval integral.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_intervalBridge (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, (1 - t) ^ n) := by sorry
