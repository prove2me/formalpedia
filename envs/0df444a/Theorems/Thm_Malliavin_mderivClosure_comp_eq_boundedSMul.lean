-- Prove2me | Theorems.Thm_Malliavin_mderivClosure_comp_eq_boundedSMul
-- name    : Malliavin.mderivClosure_comp_eq_boundedSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:35.393577+00:00
-- url     : https://prove2.me/theorems/06597ac9-7453-5711-b3f6-73ecd3308193
-- title:
--   Malliavin: mderiv Closure comp eq bounded SMul
-- statement:
--   `D̄ (φ ∘ F)` as a bounded multiple of `D̄ F`: `D̄ (φ ∘ F) = φ' (F) • D̄ F` in `L²(P; H)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L953-L965
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L953-L965

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

theorem Malliavin.mderivClosure_comp_eq_boundedSMul (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    mderivClosure P ((memLp_comp_of_deriv_le P hφ hK F).toLp _) =
      boundedSMul (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
        (C := K) (fun x ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK (F x))
        (mderivClosure P F) := by sorry
