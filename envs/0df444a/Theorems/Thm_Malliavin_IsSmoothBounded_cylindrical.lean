-- Prove2me | Theorems.Thm_Malliavin_IsSmoothBounded_cylindrical
-- name    : Malliavin.IsSmoothBounded.cylindrical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:41.17212+00:00
-- url     : https://prove2.me/theorems/c9a0435d-b320-58a4-a0fc-aba4a60485d4
-- title:
--   Is Smooth Bounded: cylindrical
-- statement:
--   Bounded `C¹` cylindrical functionals `x ↦ f (L₁ x, …, Lₙ x)` are smooth bounded.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L397-L413
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L397-L413

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
open Malliavin.IsSmoothBounded
variable {μ} {F G : W → ℝ}
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.IsSmoothBounded.cylindrical {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (L : Fin n → StrongDual ℝ W) :
    IsSmoothBounded (fun x ↦ f (fun i ↦ L i x)) := by sorry
