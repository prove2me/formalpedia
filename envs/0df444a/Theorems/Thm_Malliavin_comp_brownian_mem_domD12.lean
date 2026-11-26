-- Prove2me | Theorems.Thm_Malliavin_comp_brownian_mem_domD12
-- name    : Malliavin.comp_brownian_mem_domD12
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:14:56.107631+00:00
-- url     : https://prove2.me/theorems/5149cbdc-9fb6-5ecd-a722-f6722a65447d
-- title:
--   Malliavin: comp brownian mem dom D12
-- statement:
--   `g (B T)` lies in `𝔻₁,₂` for `g` of exponential growth.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L899-L903
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L899-L903

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

theorem Malliavin.comp_brownian_mem_domD12 (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|))
    (T : ℝ≥0) : (memLp_comp_brownian L hL hg hC hc hgb T).toLp _ ∈ domD12 P := by sorry
