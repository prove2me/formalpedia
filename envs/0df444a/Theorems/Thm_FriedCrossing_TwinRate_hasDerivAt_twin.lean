-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_twin
-- name    : FriedCrossing.TwinRate.hasDerivAt_twin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:45:29.132719+00:00
-- url     : https://prove2.me/theorems/e85ef0fd-42aa-4260-9308-c84ce8c27528
-- title:
--   Twin Rate: has Deriv At twin
-- statement:
--   The Twin Rate construction uses the has Deriv At twin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L159-L168
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L159-L168

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.hasDerivAt_twin {sStar : ℝ → ℝ} {a b a' b' : ℝ → ℝ → ℝ} {θ τ : ℝ}
    (hA : HasDerivAt (a θ) (a' θ τ) τ) (hB : HasDerivAt (b θ) (b' θ τ) τ)
    (hD : 0 < disc (a θ τ) (b θ τ)) :
    HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ := by sorry
