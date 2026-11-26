-- Prove2me | Theorems.Thm_Malliavin_inner_wienerIntegralKernel
-- name    : Malliavin.inner_wienerIntegralKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:04.01555+00:00
-- url     : https://prove2.me/theorems/0bed307c-8757-5722-80a3-327cdb0b55bb
-- title:
--   Malliavin: inner wiener Integral Kernel
-- statement:
--   The simplex Itô isometry at order one.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L486-L490
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L486-L490

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_wienerIntegralKernel (hB : IsPreBrownianReal B P) (f g : IteratedKernel 1) :
    ⟪wienerIntegralKernel hB f, wienerIntegralKernel hB g⟫_ℝ =
      ∫ t in simplex ℝ≥0 1, ⟪f t, g t⟫_ℝ ∂iteratedKernelMeasure 1 := by sorry
