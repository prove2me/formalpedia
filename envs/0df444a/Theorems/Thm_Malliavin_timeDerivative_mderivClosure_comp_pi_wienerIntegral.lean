-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_pi_wienerIntegral
-- name    : Malliavin.timeDerivative_mderivClosure_comp_pi_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:41.457787+00:00
-- url     : https://prove2.me/theorems/1ecec960-00cf-57be-92f9-c52fecbca187
-- title:
--   Malliavin: time Derivative mderiv Closure comp pi wiener Integral
-- statement:
--   **`Dₜ f (∫ g₁ dB, …, ∫ gₙ dB) = ∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)`** for `f` of class `C¹` with bounded
--   derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1149-L1170
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1149-L1170

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

theorem Malliavin.timeDerivative_mderivClosure_comp_pi_wienerIntegral (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen (mderivClosure P
        ((memLp_comp_pi P hf hK fun i ↦ wienerIntegral hB (g i)).toLp _)) =
      ∑ i, tensor (g i)
        ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral hB (g i)) i).toLp _) := by sorry
