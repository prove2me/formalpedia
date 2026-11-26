-- Prove2me | Theorems.Thm_FriedCrossing_RateRatio_ratio_tendsto
-- name    : FriedCrossing.RateRatio.ratio_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:34.312667+00:00
-- url     : https://prove2.me/theorems/a2b48e3c-3a69-41a9-8369-4fb12b4469c6
-- title:
--   Rate Ratio: ratio tendsto
-- statement:
--   z ~ a(τ−σ), p ~ b(τ−σ), b ≠ 0 ⇒ z/p → a/b.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L208-L213
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L208-L213

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio

theorem FriedCrossing.RateRatio.ratio_tendsto {z p : ℝ → ℝ} {a b σ : ℝ} (hz : LinearArrival z a σ)
    (hp : LinearArrival p b σ) (hb : b ≠ 0) :
    Tendsto (fun τ => z τ / p τ) (𝓝[≠] σ) (𝓝 (a / b)) := by sorry
