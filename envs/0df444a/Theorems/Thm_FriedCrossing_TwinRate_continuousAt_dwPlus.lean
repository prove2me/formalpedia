-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_continuousAt_dwPlus
-- name    : FriedCrossing.TwinRate.continuousAt_dwPlus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:57.858251+00:00
-- url     : https://prove2.me/theorems/d0fdfb85-41ec-4199-a5c1-3b8faa511df9
-- title:
--   Twin Rate: continuous At dw Plus
-- statement:
--   The Twin Rate construction uses the continuous At dw Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L177-L183
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L177-L183

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.continuousAt_dwPlus {p : ℝ × ℝ × ℝ × ℝ} (hD : 0 < disc p.1 p.2.1) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => dwPlus q.1 q.2.1 q.2.2.1 q.2.2.2) p := by sorry
