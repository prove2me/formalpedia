-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_wMinus_at_zero_nonneg
-- name    : FriedCrossing.PureZeros.wMinus_at_zero_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:47:46.827479+00:00
-- url     : https://prove2.me/theorems/027268a3-5a78-4074-a05e-165518d8ca43
-- title:
--   Pure Zeros: w Minus at zero nonneg
-- statement:
--   The Pure Zeros construction uses the w Minus at zero nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L300-L302
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L300-L302

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.wMinus_at_zero_nonneg {a : ℝ} (ha : 0 ≤ a) : wMinus a 0 = 0 := by sorry
