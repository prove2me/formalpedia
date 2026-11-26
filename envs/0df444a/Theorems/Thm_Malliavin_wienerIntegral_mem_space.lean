-- Prove2me | Theorems.Thm_Malliavin_wienerIntegral_mem_space
-- name    : Malliavin.wienerIntegral_mem_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:42.761424+00:00
-- url     : https://prove2.me/theorems/ab713258-93cd-5d3e-93b1-f35c6ab0bb5a
-- title:
--   Malliavin: wiener Integral mem space
-- statement:
--   Wiener integrals lie in the Cameron--Martin space.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L407-L411
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L407-L411

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

theorem Malliavin.wienerIntegral_mem_space (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) : wienerIntegral hB g ∈ Space P := by sorry
