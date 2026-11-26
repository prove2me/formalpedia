-- Prove2me | Theorems.Thm_Malliavin_norm_mderivClosure_comp_le
-- name    : Malliavin.norm_mderivClosure_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:04.630045+00:00
-- url     : https://prove2.me/theorems/a384d6df-5b95-50c0-a464-f94a627814ba
-- title:
--   Malliavin: norm mderiv Closure comp le
-- statement:
--   The closed derivative of `φ ∘ F` is controlled by that of `F`: `‖D̄ (φ ∘ F)‖ ≤ K ‖D̄ F‖`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L237-L246
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L237-L246

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
variable {φ : ℝ → ℝ} {K : ℝ≥0}

theorem Malliavin.norm_mderivClosure_comp_le (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    ‖mderivClosure μ ((memLp_comp_of_deriv_le μ hφ hK F).toLp _)‖ ≤ K * ‖mderivClosure μ F‖ := by sorry
