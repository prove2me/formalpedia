-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_boundedSMul
-- name    : Malliavin.timeDerivative_boundedSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:05.036903+00:00
-- url     : https://prove2.me/theorems/44512ba2-c828-4793-8585-a7e0c7766468
-- title:
--   Malliavin: time Derivative bounded SMul
-- statement:
--   **The time derivative commutes with bounded multipliers**:
--   `Dₜ (G • U) = G(ω) Dₜ U` for bounded measurable `G : W → ℝ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L476-L484
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L476-L484

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.timeDerivative_boundedSMul (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) {G : W → ℝ}
    (hG : AEStronglyMeasurable G P) {C : ℝ} (hC : ∀ x, |G x| ≤ C) (U : Lp (Space P) 2 P) :
    timeDerivative hB L hL hgen (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure) hG)
        (fun p ↦ hC p.2) (timeDerivative hB L hL hgen U) := by sorry
