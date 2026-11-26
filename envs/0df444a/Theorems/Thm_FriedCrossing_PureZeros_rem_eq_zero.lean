-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_rem_eq_zero
-- name    : FriedCrossing.PureZeros.rem_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:46:38.702305+00:00
-- url     : https://prove2.me/theorems/70ebf8ec-ecbc-577f-bab5-b60692b8b429
-- title:
--   Pure Zeros: rem eq zero
-- statement:
--   If the two locked branches are distinct roots of P, the remainder vanishes.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L80-L93
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L80-L93

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.rem_eq_zero {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) :
    rem₁ c₁ c₂ c₃ scl snc = 0 ∧ rem₀ c₁ c₂ c₄ scl snc = 0 := by sorry
