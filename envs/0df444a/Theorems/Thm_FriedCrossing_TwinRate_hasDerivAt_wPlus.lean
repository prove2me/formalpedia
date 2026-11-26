-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_wPlus
-- name    : FriedCrossing.TwinRate.hasDerivAt_wPlus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:59.542998+00:00
-- url     : https://prove2.me/theorems/289e98d8-fec5-51f2-82c7-ab507c7f7b3e
-- title:
--   Twin Rate: has Deriv At w Plus
-- statement:
--   The Twin Rate construction uses the has Deriv At w Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L150-L157
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L150-L157

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.hasDerivAt_wPlus {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) (hD : 0 < disc (A τ) (B τ)) :
    HasDerivAt (fun t => wPlus (A t) (B t)) (dwPlus (A τ) (B τ) a' b') τ := by sorry
