-- Prove2me | Theorems.Thm_Malliavin_mderivD12_comp
-- name    : Malliavin.mderivD12_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:58.609433+00:00
-- url     : https://prove2.me/theorems/6bfa3d30-78b0-4c2c-850c-923cbc0ec041
-- title:
--   Malliavin: mderiv D12 comp
-- statement:
--   The chain rule for the subtype map `mderivD12`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L257-L260
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L257-L260

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

theorem Malliavin.mderivD12_comp (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    mderivD12 μ (D12.comp μ hφ hK F) =
      (memLp_deriv_smul_of_deriv_le μ hφ hK F (mderivD12 μ F)).toLp _ := by sorry
