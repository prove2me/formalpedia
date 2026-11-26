-- Prove2me | Theorems.Thm_Malliavin_wienerIntegralKernel_apply
-- name    : Malliavin.wienerIntegralKernel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:40.15271+00:00
-- url     : https://prove2.me/theorems/2b6559ec-9108-5529-bbf4-f8782ec87110
-- title:
--   Malliavin: wiener Integral Kernel apply
-- statement:
--   The Malliavin construction uses the wiener Integral Kernel apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L477-L478
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L477-L478

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegralKernel_apply (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    wienerIntegralKernel hB f = wienerIntegral hB (kernelToLine f) := by sorry
