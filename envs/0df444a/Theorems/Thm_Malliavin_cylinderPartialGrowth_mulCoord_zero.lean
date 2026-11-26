-- Prove2me | Theorems.Thm_Malliavin_cylinderPartialGrowth_mulCoord_zero
-- name    : Malliavin.cylinderPartialGrowth_mulCoord_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:40.243483+00:00
-- url     : https://prove2.me/theorems/1854c7be-3fb1-4db5-990f-a3c56aff1503
-- title:
--   Malliavin: cylinder Partial Growth mul Coord zero
-- statement:
--   The partial derivatives of `B S · B T` are `B T` and `B S`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1107-L1118
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L1107-L1118

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

theorem Malliavin.cylinderPartialGrowth_mulCoord_zero (S T : ℝ≥0) :
    cylinderPartialGrowth (P := P) L hL contDiff_mulCoord zero_le_two norm_fderiv_mulCoord_le
        ![S, T] 0 = (memLp_brownian L hL T).toLp _ := by sorry
