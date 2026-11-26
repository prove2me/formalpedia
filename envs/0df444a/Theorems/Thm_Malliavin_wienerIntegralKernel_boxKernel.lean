-- Prove2me | Theorems.Thm_Malliavin_wienerIntegralKernel_boxKernel
-- name    : Malliavin.wienerIntegralKernel_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:06.777842+00:00
-- url     : https://prove2.me/theorems/0d5e7dfb-c722-433e-a510-0212ac5f4892
-- title:
--   Malliavin: wiener Integral Kernel box Kernel
-- statement:
--   The Brownian link at order one: `J₁ (1_{(a, b]}) = B b - B a`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L514-L518
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L514-L518

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegralKernel_boxKernel (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    wienerIntegralKernel hB (boxKernel (fun _ : Fin 1 ↦ a) (fun _ ↦ b)) =
      brownianLp hB b - brownianLp hB a := by sorry
