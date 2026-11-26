-- Prove2me | Theorems.Thm_Malliavin_cylinderPartialGrowth_mulCoord_one
-- name    : Malliavin.cylinderPartialGrowth_mulCoord_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:26:21.144458+00:00
-- url     : https://prove2.me/theorems/7d72a93c-7f1b-5c4f-92d7-4a972d4c8c69
-- title:
--   Malliavin: cylinder Partial Growth mul Coord one
-- statement:
--   The Malliavin construction uses the cylinder Partial Growth mul Coord one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1121-L1132
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1121-L1132

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
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.cylinderPartialGrowth_mulCoord_one (S T : ℝ≥0) :
    cylinderPartialGrowth (P := P) L hL contDiff_mulCoord zero_le_two norm_fderiv_mulCoord_le
        ![S, T] 1 = (memLp_brownian L hL S).toLp _ := by sorry
