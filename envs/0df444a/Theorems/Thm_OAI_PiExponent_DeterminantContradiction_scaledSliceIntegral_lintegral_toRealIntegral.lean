-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_lintegral_toRealIntegral
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_toRealIntegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:44:58.486209+00:00
-- url     : https://prove2.me/theorems/fa89682e-72ef-4d02-b3f1-0c18f8ae7e0b
-- title:
--   Convert the supported scaled-slice lintegral to a real integral
-- statement:
--   For every natural number n, the supported ENNReal-valued power lintegral equals the ENNReal embedding of the Bochner integral of the corresponding supported real-valued power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_toRealIntegral (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume =
      ENNReal.ofReal (∫ t : ℝ,
        (if 0 ≤ t ∧ t ≤ 1 then (1 - t) ^ n else 0)
        ∂MeasureTheory.volume) := by sorry
