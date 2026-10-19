-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitPower_intervalIntegral
-- name    : OAI.PiExponent.DeterminantContradiction.unitPower_intervalIntegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:24:58.932751+00:00
-- url     : https://prove2.me/theorems/86655528-768d-4885-a600-dceae89fefad
-- title:
--   Evaluate the unit-power interval integral
-- statement:
--   Evaluate the real interval integral of `(1 - t)^n` on `[0,1]` using its polynomial antiderivative.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.unitPower_intervalIntegral (n : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t) ^ n = 1 / (n + 1 : ℝ) := by sorry
