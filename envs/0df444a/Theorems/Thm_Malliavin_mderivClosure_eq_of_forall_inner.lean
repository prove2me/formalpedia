-- Prove2me | Theorems.Thm_Malliavin_mderivClosure_eq_of_forall_inner
-- name    : Malliavin.mderivClosure_eq_of_forall_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:06:51.859766+00:00
-- url     : https://prove2.me/theorems/a4768532-6d2b-5c3d-91f8-479c9dae9f0a
-- title:
--   Malliavin: mderiv Closure eq of forall inner
-- statement:
--   `D̄F` is determined by the duality relation, by totality of the simple vectors.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1100-L1107
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1100-L1107

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

theorem Malliavin.mderivClosure_eq_of_forall_inner {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ)
    {η : Lp (Space μ) 2 μ} (hη : ∀ k, ⟪η, simpleVec μ k⟫_ℝ = ⟪F, simpleDiv μ k⟫_ℝ) :
    mderivClosure μ F = η := by sorry
