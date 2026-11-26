-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_dwMinus_at_zero
-- name    : FriedCrossing.PureZeros.dwMinus_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:47:27.625953+00:00
-- url     : https://prove2.me/theorems/172d0573-7c7f-560a-b312-030f9148a189
-- title:
--   Pure Zeros: dw Minus at zero
-- statement:
--   At a point where b = 0 and a ≠ 0 the root through 0 has slope b'/a, whichever of w± it is.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L285-L290
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L285-L290

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.dwMinus_at_zero {a a' b' : ℝ} (ha : 0 < a) : dwMinus a 0 a' b' = b' / a := by sorry
