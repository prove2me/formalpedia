-- Prove2me | Theorems.Thm_Malliavin_cutoff_comp_mem_domD12
-- name    : Malliavin.cutoff_comp_mem_domD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:12.247877+00:00
-- url     : https://prove2.me/theorems/35ebbda8-f788-4cd8-a443-75ed21ede0ad
-- title:
--   Malliavin: cutoff comp mem dom D12
-- statement:
--   **Bounded truncations stay in `𝔻₁,₂`**: `cutoff m ∘ F ∈ 𝔻₁,₂` for every `F ∈ 𝔻₁,₂`, with
--   derivative `cutoff m' (F) • D̄ F`; these are bounded by `(m + 1) π / 2`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L269-L276
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L269-L276

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_cutoff_contDiff

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

theorem Malliavin.cutoff_comp_mem_domD12 (m : ℕ) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    (memLp_comp_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F).toLp _ ∈
        domD12 μ ∧
      mderivClosure μ
          ((memLp_comp_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F).toLp _) =
        (memLp_deriv_smul_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F
          (mderivClosure μ F)).toLp _ := by sorry
