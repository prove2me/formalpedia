-- Prove2me | Theorems.Thm_FriedCrossing_RateRatio_linearArrival_of_hasDerivAt
-- name    : FriedCrossing.RateRatio.linearArrival_of_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:30.426639+00:00
-- url     : https://prove2.me/theorems/f50cf228-18ad-5ac9-a756-678dca4c2c71
-- title:
--   Rate Ratio: linear Arrival of has Deriv At
-- statement:
--   A branch differentiable at σ and vanishing there arrives linearly with its slope.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L201-L205
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L201-L205

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio

theorem FriedCrossing.RateRatio.linearArrival_of_hasDerivAt {f : ℝ → ℝ} {c σ : ℝ} (hf : HasDerivAt f c σ)
    (h0 : f σ = 0) : LinearArrival f c σ := by sorry
