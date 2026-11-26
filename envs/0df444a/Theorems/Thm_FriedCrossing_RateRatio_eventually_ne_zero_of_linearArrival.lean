-- Prove2me | Theorems.Thm_FriedCrossing_RateRatio_eventually_ne_zero_of_linearArrival
-- name    : FriedCrossing.RateRatio.eventually_ne_zero_of_linearArrival
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:44:56.1423+00:00
-- url     : https://prove2.me/theorems/742d1dbf-f7d9-4783-b061-24ed1c69d5d1
-- title:
--   Rate Ratio: eventually ne zero of linear Arrival
-- statement:
--   The Rate Ratio construction uses the eventually ne zero of linear Arrival property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L215-L217
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L215-L217

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio

theorem FriedCrossing.RateRatio.eventually_ne_zero_of_linearArrival {f : ℝ → ℝ} {c σ : ℝ}
    (hf : LinearArrival f c σ) (hc : c ≠ 0) : ∀ᶠ τ in 𝓝[≠] σ, f τ ≠ 0 := by sorry
