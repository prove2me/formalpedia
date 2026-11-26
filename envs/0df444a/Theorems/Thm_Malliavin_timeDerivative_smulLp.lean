-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_smulLp
-- name    : Malliavin.timeDerivative_smulLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:09.16307+00:00
-- url     : https://prove2.me/theorems/73a3f10c-2c95-5395-b1ff-a93f4df35c25
-- title:
--   Malliavin: time Derivative smul Lp
-- statement:
--   The time derivative of a rank-one element `G • h` (`h` in the Cameron--Martin space) is the
--   tensor `J₁⁻¹ h ⊗ G`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L498-L506
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L498-L506

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

theorem Malliavin.timeDerivative_smulLp (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) (h : Space P) (G : Lp ℝ 2 P) :
    timeDerivative hB L hL hgen (smulLp h G) =
      tensor ((wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen) h)) G := by sorry
