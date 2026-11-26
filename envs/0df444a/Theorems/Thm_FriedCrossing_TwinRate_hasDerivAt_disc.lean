-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_disc
-- name    : FriedCrossing.TwinRate.hasDerivAt_disc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:48.331495+00:00
-- url     : https://prove2.me/theorems/5b310d92-572c-5f4b-941f-1389c893fdce
-- title:
--   Twin Rate: has Deriv At disc
-- statement:
--   The Twin Rate construction uses the has Deriv At disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L139-L148
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L139-L148

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.hasDerivAt_disc {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) :
    HasDerivAt (fun t => disc (A t) (B t)) (2 * A τ * a' - 4 * b') τ := by sorry
