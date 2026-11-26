-- Prove2me | Theorems.Thm_Malliavin_cylinder_mem_domD12_of_dominated
-- name    : Malliavin.cylinder_mem_domD12_of_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:16:20.732624+00:00
-- url     : https://prove2.me/theorems/66cb82de-3f83-4f32-a478-92744261bbde
-- title:
--   Malliavin: cylinder mem dom D12 of dominated
-- statement:
--   **Dominated cylindrical functionals lie in `𝔻₁,₂`**, and the closed Malliavin derivative is
--   the classical one: if `f` is `C¹` with `|f|, ‖f'‖ ≤ φ`, and `φ (truncCoord m L x)`,
--   `φ (L x)` are bounded by a square-integrable `ψ x`, then `x ↦ f (L₁ x, …, Lₙ x)` belongs to the
--   domain of the closure, with derivative `∑ᵢ ∂ᵢ f(L x) • ofDual Lᵢ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L303-L358
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L303-L358

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
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.cylinder_mem_domD12_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf : ∀ y, |f y| ≤ φ y) (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y)
    (hψ : ∀ m x, φ (truncCoord m L x) ≤ ψ x) (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    (memLp_cylinder_of_dominated μ hf L hφf hψ' hint).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_of_dominated μ hf L hφf hψ' hint).toLp _) =
        (memLp_mderiv_cylinder_of_dominated μ hf L hφf' hψ' hint).toLp _ := by sorry
