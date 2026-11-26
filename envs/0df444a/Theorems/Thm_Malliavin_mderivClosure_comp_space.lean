-- Prove2me | Theorems.Thm_Malliavin_mderivClosure_comp_space
-- name    : Malliavin.mderivClosure_comp_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:33.389892+00:00
-- url     : https://prove2.me/theorems/6480da72-4576-56da-8a32-2ae18a01050c
-- title:
--   Malliavin: mderiv Closure comp space
-- statement:
--   The closed derivative of `φ ∘ F` for `F` in the Cameron--Martin space is the rank-one element
--   `φ' (F) • h`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L921-L934
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L921-L934

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
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}

theorem Malliavin.mderivClosure_comp_space (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    (h : Space P) :
    mderivClosure P ((memLp_comp_of_deriv_le P hφ hK (h : Lp ℝ 2 P)).toLp _) =
      smulLp h ((memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)).toLp _) := by sorry
