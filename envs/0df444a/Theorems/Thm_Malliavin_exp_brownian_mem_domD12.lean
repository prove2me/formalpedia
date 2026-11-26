-- Prove2me | Theorems.Thm_Malliavin_exp_brownian_mem_domD12
-- name    : Malliavin.exp_brownian_mem_domD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:38:08.533544+00:00
-- url     : https://prove2.me/theorems/bd011694-8153-4540-aede-60caeb19542c
-- title:
--   Malliavin: exp brownian mem dom D12
-- statement:
--   `exp (B T)` lies in `𝔻₁,₂`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L981-L983
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L981-L983

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

theorem Malliavin.exp_brownian_mem_domD12 (T : ℝ≥0) : (memLp_exp_brownian L hL T).toLp _ ∈ domD12 P := by sorry
