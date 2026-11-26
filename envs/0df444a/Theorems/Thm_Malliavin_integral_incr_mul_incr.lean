-- Prove2me | Theorems.Thm_Malliavin_integral_incr_mul_incr
-- name    : Malliavin.integral_incr_mul_incr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:11.444474+00:00
-- url     : https://prove2.me/theorems/21e71ccf-27e4-5ed7-b242-5d198aceb41d
-- title:
--   Malliavin: integral incr mul incr
-- statement:
--   Products of increments over consecutive disjoint intervals are centered.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L678-L695
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L678-L695

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_incr_mul_incr (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    ∫ ω, (B b ω - B a ω) * (B d ω - B c ω) ∂P = 0 := by sorry
