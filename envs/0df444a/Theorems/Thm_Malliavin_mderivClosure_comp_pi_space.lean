-- Prove2me | Theorems.Thm_Malliavin_mderivClosure_comp_pi_space
-- name    : Malliavin.mderivClosure_comp_pi_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:42.3618+00:00
-- url     : https://prove2.me/theorems/83884c4b-8973-4b66-a400-dd021255b3a4
-- title:
--   Malliavin: mderiv Closure comp pi space
-- statement:
--   The closed derivative of `f (h₁, …, hₙ)` for `hᵢ` in the Cameron--Martin space is
--   `∑ᵢ ∂ᵢ f (h) • hᵢ`, a sum of rank-one elements.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1125-L1145
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1125-L1145

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

theorem Malliavin.mderivClosure_comp_pi_space {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (h : Fin n → Space P) :
    mderivClosure P ((memLp_comp_pi P hf hK fun i ↦ (h i : Lp ℝ 2 P)).toLp _) =
      ∑ i, smulLp (h i) ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _) := by sorry
