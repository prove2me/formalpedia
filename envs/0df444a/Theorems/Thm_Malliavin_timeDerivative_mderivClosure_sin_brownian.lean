-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_sin_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_sin_brownian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:42.371411+00:00
-- url     : https://prove2.me/theorems/8e45da4a-db90-5a03-be0e-4ecf107df87b
-- title:
--   Malliavin: time Derivative mderiv Closure sin brownian
-- statement:
--   **`Dₜ sin (B T) = cos (B T) 1_{(0, T]}(t)`**.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L954-L960
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L954-L960

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

theorem Malliavin.timeDerivative_mderivClosure_sin_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_sin_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_cos_brownian L hL T).toLp _) := by sorry
