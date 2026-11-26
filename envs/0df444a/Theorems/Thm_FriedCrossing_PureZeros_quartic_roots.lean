-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_quartic_roots
-- name    : FriedCrossing.PureZeros.quartic_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:57:42.519777+00:00
-- url     : https://prove2.me/theorems/27d78bad-d713-542f-9e66-baa75c361b76
-- title:
--   Pure Zeros: quartic roots
-- statement:
--   The degree-2 resonances in the disc are exactly: the two locked branches and the roots of Q.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L104-L108
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L104-L108

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.quartic_roots {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) (z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z = 0 ↔
      z = scl ∨ z = snc ∨ z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc = 0 := by sorry
