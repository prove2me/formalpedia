-- Prove2me | Theorems.Thm_Malliavin_cylinder_growth_brownian_mem_domD12
-- name    : Malliavin.cylinder_growth_brownian_mem_domD12
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:25:56.380206+00:00
-- url     : https://prove2.me/theorems/eef852f1-8f5b-4f24-9a1d-47579f691896
-- title:
--   Malliavin: cylinder growth brownian mem dom D12
-- statement:
--   **Polynomial-growth functions of Brownian coordinates lie in `𝔻₁,₂`**, with the closed
--   derivative `∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L789-L796
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L789-L796

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

theorem Malliavin.cylinder_growth_brownian_mem_domD12 {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialGrowth L hL hf hC hfg' t i) := by sorry
