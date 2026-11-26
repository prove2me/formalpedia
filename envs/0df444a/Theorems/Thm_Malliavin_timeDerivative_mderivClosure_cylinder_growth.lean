-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cylinder_growth
-- name    : Malliavin.timeDerivative_mderivClosure_cylinder_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:35.438767+00:00
-- url     : https://prove2.me/theorems/aeb59d04-fb50-5898-9493-20bce1462890
-- title:
--   Malliavin: time Derivative mderiv Closure cylinder growth
-- statement:
--   **The textbook time derivative of a polynomial-growth function of Brownian coordinates**:
--   `Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)` in `L²(ℝ≥0 × W)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L800-L808
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L800-L808

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

theorem Malliavin.timeDerivative_mderivClosure_cylinder_growth (hgen : IsWienerGenerated B) {n k : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialGrowth L hL hf hC hfg' t i) := by sorry
