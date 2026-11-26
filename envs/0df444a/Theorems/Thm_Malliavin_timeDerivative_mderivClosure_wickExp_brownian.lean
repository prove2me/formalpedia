-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_wickExp_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_wickExp_brownian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:25:57.094054+00:00
-- url     : https://prove2.me/theorems/38627500-b4ae-5b04-bd4a-03ccba90ba08
-- title:
--   Malliavin: time Derivative mderiv Closure wick Exp brownian
-- statement:
--   **`Dₜ exp (B T - T / 2) = exp (B T - T / 2) 1_{(0, T]}(t)`**: the Wick exponential is in
--   `𝔻₁,₂` and reproduces itself under the time derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L927-L934
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L927-L934

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
variable {g : ℝ → ℝ}

theorem Malliavin.timeDerivative_mderivClosure_wickExp_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_wickExp_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_wickExp_brownian L hL T).toLp _) := by sorry
