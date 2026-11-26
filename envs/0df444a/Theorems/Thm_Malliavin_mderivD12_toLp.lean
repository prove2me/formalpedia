-- Prove2me | Theorems.Thm_Malliavin_mderivD12_toLp
-- name    : Malliavin.mderivD12_toLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:04.224992+00:00
-- url     : https://prove2.me/theorems/ccb0ef30-5674-5d3d-97f1-c51eab1f94a7
-- title:
--   Malliavin: mderiv D12 to Lp
-- statement:
--   The Malliavin construction uses the mderiv D12 to Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1183-L1185
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1183-L1185

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.mderivD12_toLp {F : W → ℝ} (hF : IsSmoothBounded F) :
    mderivD12 μ ⟨hF.toLp μ, hF.toLp_mem_domD12 μ⟩ = hF.mderivLp μ := by sorry
