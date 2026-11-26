-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_wPlus_sub_wMinus
-- name    : FriedCrossing.TwinRate.wPlus_sub_wMinus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:01.430105+00:00
-- url     : https://prove2.me/theorems/13008a11-6cbd-5140-8b4e-c51449e7da09
-- title:
--   Twin Rate: w Plus sub w Minus
-- statement:
--   The Twin Rate construction uses the w Plus sub w Minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L81-L82
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L81-L82

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.wPlus_sub_wMinus (a b : ℝ) : wPlus a b - wMinus a b = Real.sqrt (disc a b) := by sorry
