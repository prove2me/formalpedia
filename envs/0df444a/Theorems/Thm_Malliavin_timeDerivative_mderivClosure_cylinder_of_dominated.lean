-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cylinder_of_dominated
-- name    : Malliavin.timeDerivative_mderivClosure_cylinder_of_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:22.190924+00:00
-- url     : https://prove2.me/theorems/9f8b4cc0-a374-501c-8f57-ae2e4c643428
-- title:
--   Malliavin: time Derivative mderiv Closure cylinder of dominated
-- statement:
--   **The textbook time derivative of a dominated function of Brownian coordinates**:
--   `Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)` in `L²(ℝ≥0 × W)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L752-L767
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L752-L767

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

theorem Malliavin.timeDerivative_mderivClosure_cylinder_of_dominated (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf : ∀ y, |f y| ≤ φ y) (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ : ∀ m x, φ (truncCoord m (fun i ↦ L (t i)) x) ≤ ψ x)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialD L hL hf hφf' t hψ' hint i) := by sorry
