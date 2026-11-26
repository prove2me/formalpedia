-- Prove2me | Theorems.Thm_Malliavin_mem_domD12_of_tendsto
-- name    : Malliavin.mem_domD12_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:11.53505+00:00
-- url     : https://prove2.me/theorems/275cb937-212f-5501-80d9-6e7ced2c75bd
-- title:
--   Malliavin: mem dom D12 of tendsto
-- statement:
--   `𝔻₁,₂` together with `mderivClosure` has a closed graph.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1149-L1154
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1149-L1154

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

theorem Malliavin.mem_domD12_of_tendsto {F : ℕ → Lp ℝ 2 μ} (hF : ∀ n, F n ∈ domD12 μ)
    {F₀ : Lp ℝ 2 μ} {η₀ : Lp (Space μ) 2 μ} (hF₀ : Tendsto F atTop (𝓝 F₀))
    (hη : Tendsto (fun n ↦ mderivClosure μ (F n)) atTop (𝓝 η₀)) :
    F₀ ∈ domD12 μ ∧ mderivClosure μ F₀ = η₀ := by sorry
