-- Prove2me | Theorems.Thm_Malliavin_expGrowth_truncCoord_le
-- name    : Malliavin.expGrowth_truncCoord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:16:29.864734+00:00
-- url     : https://prove2.me/theorems/772cb9a0-7b48-5888-bcc7-7bb9888d9cbd
-- title:
--   Malliavin: exp Growth trunc Coord le
-- statement:
--   The exponential weight of the truncated coordinates is dominated by
--   `C exp (c (∑ᵢ ‖Lᵢ‖) ‖x‖)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L451-L455
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L451-L455

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

theorem Malliavin.expGrowth_truncCoord_le {n : ℕ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (L : Fin n → StrongDual ℝ W) (m : ℕ) (x : W) :
    C * Real.exp (c * ‖truncCoord m L x‖) ≤ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)) := by sorry
