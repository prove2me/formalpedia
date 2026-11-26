-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_quartic_factor
-- name    : FriedCrossing.PureZeros.quartic_factor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:42:18.531895+00:00
-- url     : https://prove2.me/theorems/f8e73013-2b62-4d1c-aaa9-9615000b32fc
-- title:
--   Pure Zeros: quartic factor
-- statement:
--   P factors exactly through the pure quadratic.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L96-L101
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L96-L101

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.quartic_factor {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) (z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z =
      (z - scl) * (z - snc) * (z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc) := by sorry
