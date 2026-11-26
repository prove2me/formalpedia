-- Prove2me | Theorems.Thm_Malliavin_inner_mderivClosure_simpleVec
-- name    : Malliavin.inner_mderivClosure_simpleVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:31.812115+00:00
-- url     : https://prove2.me/theorems/29c5a81a-28e1-40fa-b47a-ab63a8d6a3e6
-- title:
--   Malliavin: inner mderiv Closure simple Vec
-- statement:
--   **Duality on `𝔻₁,₂`**: the adjoint relation `⟪D̄F, G • h⟫ = ⟪F, G h - ⟪DG, h⟫⟫` extends by
--   continuity from smooth bounded functionals to the whole Sobolev space.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1084-L1097
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1084-L1097

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

theorem Malliavin.inner_mderivClosure_simpleVec {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) (k : SimpleIndex μ) :
    ⟪mderivClosure μ F, simpleVec μ k⟫_ℝ = ⟪F, simpleDiv μ k⟫_ℝ := by sorry
