-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_inner_integral_zero_eq_zero
-- name    : Malliavin.IteratedIntegralFamily.inner_integral_zero_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:32.703443+00:00
-- url     : https://prove2.me/theorems/5fc88c27-2ae9-4f4a-a34b-db3a0088e867
-- title:
--   Iterated Integral Family: inner integral zero eq zero
-- statement:
--   Zero-order integrals of any family are orthogonal to centered random variables.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L887-L898
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L887-L898

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.inner_integral_zero_eq_zero (J : IteratedIntegralFamily P)
    {Y : RandomL2 P} (hY : ∫ ω, Y ω ∂P = 0) (f : IteratedKernel 0) :
    ⟪Y, J.integral 0 f⟫_ℝ = 0 := by sorry
