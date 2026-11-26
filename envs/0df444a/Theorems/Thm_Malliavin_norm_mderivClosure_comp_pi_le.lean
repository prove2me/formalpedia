-- Prove2me | Theorems.Thm_Malliavin_norm_mderivClosure_comp_pi_le
-- name    : Malliavin.norm_mderivClosure_comp_pi_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:29.406271+00:00
-- url     : https://prove2.me/theorems/bcac37d2-f6e8-5f92-bd2e-bbf54930092c
-- title:
--   Malliavin: norm mderiv Closure comp pi le
-- statement:
--   `‖D̄ f(F)‖ ≤ K ∑ᵢ ‖D̄ Fᵢ‖`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L841-L879
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L841-L879

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

theorem Malliavin.norm_mderivClosure_comp_pi_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 μ} (hF : ∀ i, F i ∈ domD12 μ) :
    ‖mderivClosure μ ((memLp_comp_pi μ hf hK F).toLp _)‖ ≤
      K * ∑ i, ‖mderivClosure μ (F i)‖ := by sorry
