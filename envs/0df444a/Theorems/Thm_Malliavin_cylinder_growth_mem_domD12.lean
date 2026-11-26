-- Prove2me | Theorems.Thm_Malliavin_cylinder_growth_mem_domD12
-- name    : Malliavin.cylinder_growth_mem_domD12
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:36:13.825096+00:00
-- url     : https://prove2.me/theorems/18ca33f4-7b23-5f22-8fa1-de8a7af6b8c0
-- title:
--   Malliavin: cylinder growth mem dom D12
-- statement:
--   **Cylindrical functionals of polynomial growth lie in `𝔻₁,₂`**, and the closed Malliavin
--   derivative is the classical one: if `f` is `C¹` with `|f|` and `‖f'‖` of polynomial growth,
--   then `x ↦ f (L₁ x, …, Lₙ x)` belongs to the domain of the closure, with derivative
--   `∑ᵢ ∂ᵢ f(L x) • ofDual Lᵢ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L406-L413
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L406-L413

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

theorem Malliavin.cylinder_growth_mem_domD12 {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (L : Fin n → StrongDual ℝ W) :
    (memLp_cylinder_growth μ hf hC hfg L).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_growth μ hf hC hfg L).toLp _) =
        (memLp_mderiv_cylinder_growth μ hf hC hfg' L).toLp _ := by sorry
