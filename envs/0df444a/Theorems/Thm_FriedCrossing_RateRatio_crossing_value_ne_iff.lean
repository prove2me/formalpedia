-- Prove2me | Theorems.Thm_FriedCrossing_RateRatio_crossing_value_ne_iff
-- name    : FriedCrossing.RateRatio.crossing_value_ne_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:06.391841+00:00
-- url     : https://prove2.me/theorems/5cbdd8f5-913b-493c-88be-72acb434b9bd
-- title:
--   Rate Ratio: crossing value ne iff
-- statement:
--   The crossing value differs from τ_R exactly when the rates are unbalanced.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L220-L228
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L220-L228

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio

theorem FriedCrossing.RateRatio.crossing_value_ne_iff {τR a b : ℝ} (hτR : τR ≠ 0) (ha : a ≠ 0) :
    τR * (b / a) ≠ τR ↔ b ≠ a := by sorry
