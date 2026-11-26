-- Prove2me | Theorems.Thm_Malliavin_stepSum_single_add
-- name    : Malliavin.stepSum_single_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:17.894035+00:00
-- url     : https://prove2.me/theorems/c39e55fd-2308-5842-827d-ee76fa98b2b5
-- title:
--   Malliavin: step Sum single add
-- statement:
--   The Malliavin construction uses the step Sum single add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L770-L776
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L770-L776

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin
omit [MeasurableSpace Ω]

theorem Malliavin.stepSum_single_add (t : ℝ≥0) (c : ℝ) (v : ℝ≥0 →₀ ℝ) :
    stepSum B (Finsupp.single t c + v) = fun ω ↦ c * B t ω + stepSum B v ω := by sorry
