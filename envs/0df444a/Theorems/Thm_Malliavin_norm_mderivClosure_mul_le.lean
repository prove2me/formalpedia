-- Prove2me | Theorems.Thm_Malliavin_norm_mderivClosure_mul_le
-- name    : Malliavin.norm_mderivClosure_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:13.978308+00:00
-- url     : https://prove2.me/theorems/8b53dfe4-ca88-5848-b9ef-c9607db8835b
-- title:
--   Malliavin: norm mderiv Closure mul le
-- statement:
--   Norm bound for the product rule: `‖D̄ (F G)‖ ≤ D' ‖F‖ + D ‖D̄ F‖` where `|G| ≤ D` and
--   `‖D G‖ ≤ D'`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L417-L454
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L417-L454

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
variable {G : W → ℝ}

theorem Malliavin.norm_mderivClosure_mul_le (hG : IsSmoothBounded G) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ)
    {D D' : ℝ} (hD : ∀ x, |G x| ≤ D) (hD' : ∀ x, ‖mderiv μ G x‖ ≤ D') :
    ‖mderivClosure μ ((memLp_mul_smoothBounded μ hG F).toLp _)‖ ≤
      D' * ‖F‖ + D * ‖mderivClosure μ F‖ := by sorry
