-- Prove2me | Theorems.Thm_FriedCrossing_RateRatio_crossing_value_local
-- name    : FriedCrossing.RateRatio.crossing_value_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:38.937235+00:00
-- url     : https://prove2.me/theorems/239b999c-65bf-4c31-9de8-d169bcbd2803
-- title:
--   Rate Ratio: crossing value local
-- statement:
--   `crossing_value` with the off-crossing identity only required EVENTUALLY near σ.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L308-L319
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L308-L319

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.RateRatio

theorem FriedCrossing.RateRatio.crossing_value_local {z p R : ℝ → ℝ} {a b σ τR : ℝ}
    (hz : LinearArrival z a σ) (hp : LinearArrival p b σ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hoff : ∀ᶠ τ in 𝓝[≠] σ, R τ * z τ / p τ = τR) (hR : ContinuousAt R σ) :
    R σ = τR * (b / a) := by sorry
