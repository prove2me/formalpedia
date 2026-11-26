-- Prove2me | Theorems.Thm_Malliavin_integral_incr_mul_incr_mul_eval
-- name    : Malliavin.integral_incr_mul_incr_mul_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:41.868568+00:00
-- url     : https://prove2.me/theorems/202567f8-9993-5546-a569-c8b00a045473
-- title:
--   Malliavin: integral incr mul incr mul eval
-- statement:
--   Expectation of an odd polynomial: `E[(B b - B a) (B d - B c) B t] = 0`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L619-L630
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L619-L630

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_incr_mul_incr_mul_eval (hB : IsPreBrownianReal B P) (a b c d t : ℝ≥0) :
    ∫ ω, (B b ω - B a ω) * (B d ω - B c ω) * B t ω ∂P = 0 := by sorry
