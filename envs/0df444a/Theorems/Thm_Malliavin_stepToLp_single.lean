-- Prove2me | Theorems.Thm_Malliavin_stepToLp_single
-- name    : Malliavin.stepToLp_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:56.455436+00:00
-- url     : https://prove2.me/theorems/c1ce48b7-0024-4a09-83b1-a1079cee7056
-- title:
--   Malliavin: step To Lp single
-- statement:
--   The Malliavin construction uses the step To Lp single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L240-L242
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L240-L242

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.stepToLp_single (t : ℝ≥0) (c : ℝ) :
    stepToLp (Finsupp.single t c) = c • intervalIndicator t := by sorry
