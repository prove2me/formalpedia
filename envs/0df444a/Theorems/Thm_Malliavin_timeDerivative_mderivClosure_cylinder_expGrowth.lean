-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cylinder_expGrowth
-- name    : Malliavin.timeDerivative_mderivClosure_cylinder_expGrowth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:25:48.628604+00:00
-- url     : https://prove2.me/theorems/de88a8b6-340f-5629-885f-d469ec6766c5
-- title:
--   Malliavin: time Derivative mderiv Closure cylinder exp Growth
-- statement:
--   **The textbook time derivative of an exponential-growth function of Brownian
--   coordinates**: `Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L845-L854
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L845-L854

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

theorem Malliavin.timeDerivative_mderivClosure_cylinder_expGrowth (hgen : IsWienerGenerated B) {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialExp L hL hf hC hc hfg' t i) := by sorry
