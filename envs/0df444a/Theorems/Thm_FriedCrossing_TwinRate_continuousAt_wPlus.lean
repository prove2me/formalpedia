-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_continuousAt_wPlus
-- name    : FriedCrossing.TwinRate.continuousAt_wPlus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:00.707972+00:00
-- url     : https://prove2.me/theorems/0f8c8657-12f9-5994-9dcf-0420f374d821
-- title:
--   Twin Rate: continuous At w Plus
-- statement:
--   The Twin Rate construction uses the continuous At w Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L172-L175
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L172-L175

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.continuousAt_wPlus (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => wPlus q.1 q.2) p := by sorry
