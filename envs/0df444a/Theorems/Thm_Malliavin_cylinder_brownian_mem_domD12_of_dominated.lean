-- Prove2me | Theorems.Thm_Malliavin_cylinder_brownian_mem_domD12_of_dominated
-- name    : Malliavin.cylinder_brownian_mem_domD12_of_dominated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:17:05.038809+00:00
-- url     : https://prove2.me/theorems/82225fec-0d43-4fde-bc77-429ff355f4d3
-- title:
--   Malliavin: cylinder brownian mem dom D12 of dominated
-- statement:
--   **Dominated functions of Brownian coordinates lie in `𝔻₁,₂`**, with the closed derivative
--   `∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L710-L748
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L710-L748

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

theorem Malliavin.cylinder_brownian_mem_domD12_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ : ∀ m x, φ (truncCoord m (fun i ↦ L (t i)) x) ≤ ψ x)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i) := by sorry
