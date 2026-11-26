-- Prove2me | Theorems.Thm_Malliavin_inner_mderivClosure_const
-- name    : Malliavin.inner_mderivClosure_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:14.711001+00:00
-- url     : https://prove2.me/theorems/d86f1bc7-aa32-555d-90e7-b6b55433dd31
-- title:
--   Malliavin: inner mderiv Closure const
-- statement:
--   **Integration by parts on `𝔻₁,₂`**: `∫ ⟪D̄F, h⟫ dμ = ∫ F · h dμ`, i.e.
--   `⟪D̄F, const h⟫_{L²(μ;H)} = ⟪F, h⟫_{L²(μ)}`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1351-L1354
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1351-L1354

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

theorem Malliavin.inner_mderivClosure_const {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) (h : Space μ) :
    ⟪mderivClosure μ F, (memLp_const h).toLp (fun _ ↦ h)⟫_ℝ = ⟪F, (h : Lp ℝ 2 μ)⟫_ℝ := by sorry
