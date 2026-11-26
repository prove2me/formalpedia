-- Prove2me | Theorems.Thm_Malliavin_stepToRandom_single
-- name    : Malliavin.stepToRandom_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:50:27.816933+00:00
-- url     : https://prove2.me/theorems/8d632ef3-6257-4f96-b14a-7f96b41e8ad7
-- title:
--   Malliavin: step To Random single
-- statement:
--   The Malliavin construction uses the step To Random single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L244-L246
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L244-L246

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.stepToRandom_single (hB : IsPreBrownianReal B P) (t : ℝ≥0) (c : ℝ) :
    stepToRandom hB (Finsupp.single t c) = c • brownianLp hB t := by sorry
