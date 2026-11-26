-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_wienerIntegral
-- name    : Malliavin.timeDerivative_mderivClosure_comp_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:49.326989+00:00
-- url     : https://prove2.me/theorems/2d304e7d-d659-4f77-ab13-90543c2bff40
-- title:
--   Malliavin: time Derivative mderiv Closure comp wiener Integral
-- statement:
--   **`Dₜ φ (∫ g dB) = φ' (∫ g dB) g(t)`** for `φ` of class `C¹` with bounded derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L937-L948
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L937-L948

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}

theorem Malliavin.timeDerivative_mderivClosure_comp_wienerIntegral (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_comp_of_deriv_le P hφ hK (wienerIntegral hB g)).toLp _)) =
      tensor g ((memLp_deriv_comp hφ hK (wienerIntegral hB g)).toLp _) := by sorry
