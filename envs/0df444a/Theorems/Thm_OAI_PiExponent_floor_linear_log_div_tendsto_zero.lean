-- Prove2me | Theorems.Thm_OAI_PiExponent_floor_linear_log_div_tendsto_zero
-- name    : OAI.PiExponent.floor_linear_log_div_tendsto_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:43:00.456835+00:00
-- url     : https://prove2.me/theorems/118fbb74-8430-4f0d-83f1-36143500e6b6
-- title:
--   Floor-linear counts have vanishing logarithmic rate
-- statement:
--   For every positive real c, the logarithm of the natural floor of H/c plus one, divided by H, tends to zero as H tends to positive infinity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent

theorem OAI.PiExponent.floor_linear_log_div_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun H : ℝ => Real.log ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 0) := by sorry
