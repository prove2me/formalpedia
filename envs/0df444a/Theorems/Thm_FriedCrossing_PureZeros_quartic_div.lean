-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_quartic_div
-- name    : FriedCrossing.PureZeros.quartic_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:17.56044+00:00
-- url     : https://prove2.me/theorems/ec1881f4-3be6-5bc6-b364-b62613ff047f
-- title:
--   Pure Zeros: quartic div
-- statement:
--   Division with remainder: P = (z − s_cl)(z − s_nc)·Q − rem₁·z + rem₀.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L73-L77
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L73-L77

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.quartic_div (c₁ c₂ c₃ c₄ scl snc z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z =
      (z - scl) * (z - snc) * (z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc)
        - rem₁ c₁ c₂ c₃ scl snc * z + rem₀ c₁ c₂ c₄ scl snc := by sorry
