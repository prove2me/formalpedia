-- Prove2me | Theorems.Thm_Malliavin_cylinder_expGrowth_mem_domD12
-- name    : Malliavin.cylinder_expGrowth_mem_domD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:26:26.886829+00:00
-- url     : https://prove2.me/theorems/6d016b25-8c9c-4581-9fa9-e8e4bdb7d203
-- title:
--   Malliavin: cylinder exp Growth mem dom D12
-- statement:
--   **Cylindrical functionals of exponential growth lie in `𝔻₁,₂`**, with the classical
--   derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L496-L504
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L496-L504

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

theorem Malliavin.cylinder_expGrowth_mem_domD12 {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (L : Fin n → StrongDual ℝ W) :
    (memLp_cylinder_expGrowth μ hf hC hc hfg L).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_expGrowth μ hf hC hc hfg L).toLp _) =
        (memLp_mderiv_cylinder_expGrowth μ hf hC hc hfg' L).toLp _ := by sorry
