-- Prove2me | Theorems.Thm_Malliavin_polynomial_brownian_mem_domD12
-- name    : Malliavin.polynomial_brownian_mem_domD12
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:59.280575+00:00
-- url     : https://prove2.me/theorems/71df3812-4fee-51c6-a49a-b728a4fe374d
-- title:
--   Malliavin: polynomial brownian mem dom D12
-- statement:
--   `p (B T)` lies in `𝔻₁,₂` for every real polynomial `p`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1013-L1017
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1013-L1017

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
variable {g : ℝ → ℝ}

theorem Malliavin.polynomial_brownian_mem_domD12 (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian L hL p T).toLp _ ∈ domD12 P := by sorry
