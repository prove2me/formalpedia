-- Prove2me | Theorems.Thm_Malliavin_mderivClosure_comp_pi_eq_sum_boundedSMul
-- name    : Malliavin.mderivClosure_comp_pi_eq_sum_boundedSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:45.351833+00:00
-- url     : https://prove2.me/theorems/c7e83829-cd70-415d-a80e-d094c1d56f51
-- title:
--   Malliavin: mderiv Closure comp pi eq sum bounded SMul
-- statement:
--   `D̄ f(F)` as a sum of bounded multiples of the `D̄ Fᵢ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1080-L1100
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1080-L1100

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

theorem Malliavin.mderivClosure_comp_pi_eq_sum_boundedSMul {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 P}
    (hF : ∀ i, F i ∈ domD12 P) :
    mderivClosure P ((memLp_comp_pi P hf hK F).toLp _) =
      ∑ i, boundedSMul (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
        (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
        (fun _ ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i)) := by sorry
