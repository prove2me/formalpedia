-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_wMinus_at_cddp
-- name    : FriedCrossing.TwinRate.wMinus_at_cddp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:16.873412+00:00
-- url     : https://prove2.me/theorems/33e5f278-cc8c-521e-951a-308e55404a51
-- title:
--   Twin Rate: w Minus at cddp
-- statement:
--   The Twin Rate construction uses the w Minus at cddp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L95-L97
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L95-L97

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.wMinus_at_cddp {r₀ : ℝ} (hr₀ : 0 < r₀) : wMinus r₀ 0 = 0 := by sorry
