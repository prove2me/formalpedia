-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_wMinus_at_zero_neg
-- name    : FriedCrossing.PureZeros.wMinus_at_zero_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:03.088995+00:00
-- url     : https://prove2.me/theorems/c57a5c65-f298-46c5-a074-ef07512d4345
-- title:
--   Pure Zeros: w Minus at zero neg
-- statement:
--   The Pure Zeros construction uses the w Minus at zero neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L311-L314
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L311-L314

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.wMinus_at_zero_neg {a : ℝ} (ha : a < 0) : wMinus a 0 = a := by sorry
