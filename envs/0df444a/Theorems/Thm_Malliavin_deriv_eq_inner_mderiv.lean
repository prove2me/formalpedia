-- Prove2me | Theorems.Thm_Malliavin_deriv_eq_inner_mderiv
-- name    : Malliavin.deriv_eq_inner_mderiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:41.876048+00:00
-- url     : https://prove2.me/theorems/532a208b-b6bb-58a6-8ade-7c6e4e8f196b
-- title:
--   Malliavin: deriv eq inner mderiv
-- statement:
--   The derivative in the direction `inclusion μ h` equals `⟪DF x, h⟫`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L304-L307
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L304-L307

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

theorem Malliavin.deriv_eq_inner_mderiv {F : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (h : Space μ) :
    deriv (fun ε : ℝ ↦ F (x + ε • inclusion μ h)) 0 = ⟪mderiv μ F x, h⟫_ℝ := by sorry
