-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_interval_eval
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_interval_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:38:44.075233+00:00
-- url     : https://prove2.me/theorems/7107cb1e-9fe6-4f32-9dfa-5c6ec7d49947
-- title:
--   Evaluate the real scaled-slice interval integral
-- statement:
--   The real interval integral of (1 - t) to the natural power n on [0,1] is the reciprocal of n + 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_interval_eval (n : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t) ^ n = ((n : ℝ) + 1)⁻¹ := by sorry
