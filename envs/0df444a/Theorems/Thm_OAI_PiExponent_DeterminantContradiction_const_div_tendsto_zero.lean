-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_const_div_tendsto_zero
-- name    : OAI.PiExponent.DeterminantContradiction.const_div_tendsto_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:46:20.811979+00:00
-- url     : https://prove2.me/theorems/a6681e65-b5fc-43a4-80bc-6c137a5b6023
-- title:
--   A fixed real constant divided by H tends to zero
-- statement:
--   Any fixed real constant divided by H tends to zero as H tends to infinity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Topology
open Filter

theorem OAI.PiExponent.DeterminantContradiction.const_div_tendsto_zero (c : ℝ) : Tendsto (fun H : ℝ => c / H) atTop (𝓝 0) := by sorry
