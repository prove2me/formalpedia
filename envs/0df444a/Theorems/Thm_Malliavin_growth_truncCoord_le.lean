-- Prove2me | Theorems.Thm_Malliavin_growth_truncCoord_le
-- name    : Malliavin.growth_truncCoord_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:20.601925+00:00
-- url     : https://prove2.me/theorems/93af5862-03fe-5bdd-ba2b-a6aa85444a13
-- title:
--   Malliavin: growth trunc Coord le
-- statement:
--   The growth weight `C (1 + ‖y‖)ᵏ` of the truncated coordinates is dominated by the Gaussian
--   weight.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L365-L370
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L365-L370

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

theorem Malliavin.growth_truncCoord_le {n k : ℕ} {C : ℝ} (hC : 0 ≤ C) (L : Fin n → StrongDual ℝ W)
    (m : ℕ) (x : W) :
    C * (1 + ‖truncCoord m L x‖) ^ k ≤ C * gaussWeight L x ^ k := by sorry
