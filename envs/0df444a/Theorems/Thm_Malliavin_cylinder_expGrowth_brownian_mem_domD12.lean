-- Prove2me | Theorems.Thm_Malliavin_cylinder_expGrowth_brownian_mem_domD12
-- name    : Malliavin.cylinder_expGrowth_brownian_mem_domD12
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:25:47.677845+00:00
-- url     : https://prove2.me/theorems/123747c4-effe-4fd0-8d42-cc9978f24c7c
-- title:
--   Malliavin: cylinder exp Growth brownian mem dom D12
-- statement:
--   **Exponential-growth functions of Brownian coordinates lie in `𝔻₁,₂`**, with the closed
--   derivative `∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L832-L841
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L832-L841

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

theorem Malliavin.cylinder_expGrowth_brownian_mem_domD12 {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialExp L hL hf hC hc hfg' t i) := by sorry
