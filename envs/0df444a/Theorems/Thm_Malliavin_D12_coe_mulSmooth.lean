-- Prove2me | Theorems.Thm_Malliavin_D12_coe_mulSmooth
-- name    : Malliavin.D12.coe_mulSmooth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:42:45.811795+00:00
-- url     : https://prove2.me/theorems/a1c8f2ad-a935-48d6-b13a-d23c51f68c5f
-- title:
--   D12: coe mul Smooth
-- statement:
--   The D12 construction uses the coe mul Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L460-L461
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L460-L461

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

theorem Malliavin.D12.coe_mulSmooth (hG : IsSmoothBounded G) (F : D12 μ) :
    (D12.mulSmooth μ hG F : Lp ℝ 2 μ) = (memLp_mul_smoothBounded μ hG F).toLp _ := by sorry
