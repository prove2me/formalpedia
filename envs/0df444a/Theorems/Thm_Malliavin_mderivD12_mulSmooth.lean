-- Prove2me | Theorems.Thm_Malliavin_mderivD12_mulSmooth
-- name    : Malliavin.mderivD12_mulSmooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:26.022887+00:00
-- url     : https://prove2.me/theorems/887ba598-63a9-5d54-9539-3454a3dc221d
-- title:
--   Malliavin: mderiv D12 mul Smooth
-- statement:
--   The product rule for the subtype map `mderivD12`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L464-L466
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L464-L466

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

theorem Malliavin.mderivD12_mulSmooth (hG : IsSmoothBounded G) (F : D12 μ) :
    mderivD12 μ (D12.mulSmooth μ hG F) = (memLp_mul_deriv μ hG F (mderivD12 μ F)).toLp _ := by sorry
