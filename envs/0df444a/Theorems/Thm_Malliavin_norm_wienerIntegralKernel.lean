-- Prove2me | Theorems.Thm_Malliavin_norm_wienerIntegralKernel
-- name    : Malliavin.norm_wienerIntegralKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:13.848813+00:00
-- url     : https://prove2.me/theorems/80b835f9-df0a-5639-b466-f54e8c9bce9f
-- title:
--   Malliavin: norm wiener Integral Kernel
-- statement:
--   The Malliavin construction uses the norm wiener Integral Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L496-L498
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L496-L498

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.norm_wienerIntegralKernel (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    ‖wienerIntegralKernel hB f‖ = ‖f‖ := by sorry
