-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_continuousAt_wMinus
-- name    : FriedCrossing.PureZeros.continuousAt_wMinus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:19.90891+00:00
-- url     : https://prove2.me/theorems/46558d50-3746-4cfc-9cfd-8b0f91bdfec1
-- title:
--   Pure Zeros: continuous At w Minus
-- statement:
--   The Pure Zeros construction uses the continuous At w Minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L279-L282
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L279-L282

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.continuousAt_wMinus (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => wMinus q.1 q.2) p := by sorry
