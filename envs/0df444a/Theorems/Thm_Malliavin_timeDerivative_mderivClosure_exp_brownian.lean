-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_exp_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_exp_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:24.571874+00:00
-- url     : https://prove2.me/theorems/cd17c76c-fe73-4789-b8f2-36f35922ebc5
-- title:
--   Malliavin: time Derivative mderiv Closure exp brownian
-- statement:
--   **`exp (B T) ∈ 𝔻₁,₂` with `Dₜ exp (B T) = exp (B T) 1_{(0, T]}(t)`**.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L910-L916
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L910-L916

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

theorem Malliavin.timeDerivative_mderivClosure_exp_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_exp_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_exp_brownian L hL T).toLp _) := by sorry
