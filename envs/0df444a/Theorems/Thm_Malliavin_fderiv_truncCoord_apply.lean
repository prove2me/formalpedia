-- Prove2me | Theorems.Thm_Malliavin_fderiv_truncCoord_apply
-- name    : Malliavin.fderiv_truncCoord_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:26:40.329167+00:00
-- url     : https://prove2.me/theorems/ee720ccf-c449-48fa-89ac-b7f495f6aed1
-- title:
--   Malliavin: fderiv trunc Coord apply
-- statement:
--   The derivative of the truncated coordinate map, applied to a vector.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L162-L176
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L162-L176

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
  (μ : Measure W) [IsGaussian μ]
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ]

theorem Malliavin.fderiv_truncCoord_apply (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x w : W) :
    fderiv ℝ (truncCoord m L) x w =
      ∑ i, (deriv (cutoff m) (L i x) * L i w) • Pi.single i (1 : ℝ) := by sorry
