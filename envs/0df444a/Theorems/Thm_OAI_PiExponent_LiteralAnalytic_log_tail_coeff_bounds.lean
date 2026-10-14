-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_log_tail_coeff_bounds
-- name    : OAI.PiExponent.LiteralAnalytic.log_tail_coeff_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T13:34:29.365639+00:00
-- url     : https://prove2.me/theorems/5129e0f3-4ebc-4608-a56f-f2d30684ee64
-- title:
--   Coefficient bounds and strict support for logarithm tails
-- statement:
--   Shows that every coefficient of the truncated logarithm tail has norm at most one and that coefficients vanish strictly below the truncation cutoff. The coefficient at degree exactly `T` is not claimed to vanish.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.log_tail_coeff_bounds
    (T n : ℕ) :
    ‖PowerSeries.coeff n (RowTranslation.tail T (PowerSeries.log ℂ))‖ ≤ 1 ∧
      (n < T → PowerSeries.coeff n (RowTranslation.tail T (PowerSeries.log ℂ)) = 0) := by sorry
