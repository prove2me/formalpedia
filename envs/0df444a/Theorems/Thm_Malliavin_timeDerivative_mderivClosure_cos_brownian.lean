-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cos_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_cos_brownian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:38:00.315496+00:00
-- url     : https://prove2.me/theorems/25fb09c6-73e2-4b2a-853c-01e8efe691da
-- title:
--   Malliavin: time Derivative mderiv Closure cos brownian
-- statement:
--   **`Dₜ cos (B T) = -sin (B T) 1_{(0, T]}(t)`**.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L963-L978
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L963-L978

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

theorem Malliavin.timeDerivative_mderivClosure_cos_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_cos_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) (-(memLp_sin_brownian L hL T).toLp _) := by sorry
