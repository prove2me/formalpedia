-- Prove2me | Theorems.Thm_Malliavin_integral_wienerIntegralKernel
-- name    : Malliavin.integral_wienerIntegralKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:00:08.540783+00:00
-- url     : https://prove2.me/theorems/84b042b8-b3ff-486e-ae4e-41705bfe690d
-- title:
--   Malliavin: integral wiener Integral Kernel
-- statement:
--   The Malliavin construction uses the integral wiener Integral Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L492-L494
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L492-L494

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_wienerIntegralKernel (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    ∫ ω, wienerIntegralKernel hB f ω ∂P = 0 := by sorry
