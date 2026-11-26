-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_polynomial_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_polynomial_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:53.72863+00:00
-- url     : https://prove2.me/theorems/a512be7c-6757-5534-bfad-30680936468f
-- title:
--   Malliavin: time Derivative mderiv Closure polynomial brownian
-- statement:
--   **`Dₜ p (B T) = p' (B T) 1_{(0, T]}(t)`** for every real polynomial `p`; in particular all
--   polynomials in a Brownian coordinate lie in `𝔻₁,₂`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1001-L1010
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1001-L1010

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

theorem Malliavin.timeDerivative_mderivClosure_polynomial_brownian (hgen : IsWienerGenerated B)
    (p : Polynomial ℝ) (T : ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_polynomial_brownian L hL p T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_polynomial_derivative_brownian L hL p T).toLp _) := by sorry
