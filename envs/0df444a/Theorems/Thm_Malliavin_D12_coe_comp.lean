-- Prove2me | Theorems.Thm_Malliavin_D12_coe_comp
-- name    : Malliavin.D12.coe_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:30.109825+00:00
-- url     : https://prove2.me/theorems/dd986ad3-3d4e-4fa4-aac4-b09c0b0781fc
-- title:
--   D12: coe comp
-- statement:
--   The D12 construction uses the coe comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L253-L254
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L253-L254

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

theorem Malliavin.D12.coe_comp (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    (D12.comp μ hφ hK F : Lp ℝ 2 μ) = (memLp_comp_of_deriv_le μ hφ hK F).toLp _ := by sorry
