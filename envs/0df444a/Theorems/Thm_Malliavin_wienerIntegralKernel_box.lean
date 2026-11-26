-- Prove2me | Theorems.Thm_Malliavin_wienerIntegralKernel_box
-- name    : Malliavin.wienerIntegralKernel_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:29.772368+00:00
-- url     : https://prove2.me/theorems/15ba47fd-1793-4451-b099-ae6f985ce883
-- title:
--   Malliavin: wiener Integral Kernel box
-- statement:
--   The genuine `J₁` satisfies the order-one clause of the Brownian link.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L521-L531
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L521-L531

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegralKernel_box (hB : IsPreBrownianReal B P) (u v : Fin 1 → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) :
    (fun ω ↦ wienerIntegralKernel hB (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v := by sorry
