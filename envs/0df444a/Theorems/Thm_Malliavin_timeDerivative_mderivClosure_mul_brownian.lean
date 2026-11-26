-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_mul_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_mul_brownian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:38:26.504796+00:00
-- url     : https://prove2.me/theorems/1a15f1c6-041b-4239-b639-f84c1faaf05e
-- title:
--   Malliavin: time Derivative mderiv Closure mul brownian
-- statement:
--   **`Dₜ (B S · B T) = B T 1_{(0, S]}(t) + B S 1_{(0, T]}(t)`**.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1135-L1143
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1135-L1143

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL

theorem Malliavin.timeDerivative_mderivClosure_mul_brownian (hgen : IsWienerGenerated B) (S T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_mul_brownian L hL S T).toLp _)) =
      tensor (intervalIndicator S) ((memLp_brownian L hL T).toLp _) +
        tensor (intervalIndicator T) ((memLp_brownian L hL S).toLp _) := by sorry
