-- Prove2me | Theorems.Thm_Malliavin_brownianLp_mem_domD12
-- name    : Malliavin.brownianLp_mem_domD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:33:49.081797+00:00
-- url     : https://prove2.me/theorems/02f69821-ae76-473d-8b1e-3726f8d5390b
-- title:
--   Malliavin: brownian Lp mem dom D12
-- statement:
--   Brownian coordinates lie in `𝔻₁,₂`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L277-L280
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L277-L280

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.brownianLp_mem_domD12 (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t ∈ domD12 P := by sorry
