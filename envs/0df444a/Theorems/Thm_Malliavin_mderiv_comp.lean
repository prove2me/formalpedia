-- Prove2me | Theorems.Thm_Malliavin_mderiv_comp
-- name    : Malliavin.mderiv_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:15.728676+00:00
-- url     : https://prove2.me/theorems/00c479c8-1057-5fda-8d6a-2fea2f13662f
-- title:
--   Malliavin: mderiv comp
-- statement:
--   **Chain rule** for a post-composition with a differentiable `φ : ℝ → ℝ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L345-L354
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L345-L354

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

theorem Malliavin.mderiv_comp {F : W → ℝ} {x : W} {φ : ℝ → ℝ} (hφ : DifferentiableAt ℝ φ (F x))
    (hF : DifferentiableAt ℝ F x) :
    mderiv μ (fun y ↦ φ (F y)) x = deriv φ (F x) • mderiv μ F x := by sorry
