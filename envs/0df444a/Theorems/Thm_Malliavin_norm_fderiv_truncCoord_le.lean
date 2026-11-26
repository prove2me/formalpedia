-- Prove2me | Theorems.Thm_Malliavin_norm_fderiv_truncCoord_le
-- name    : Malliavin.norm_fderiv_truncCoord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:25:10.792814+00:00
-- url     : https://prove2.me/theorems/8130b626-3485-4855-9f52-858681520ed4
-- title:
--   Malliavin: norm fderiv trunc Coord le
-- statement:
--   The derivative of the truncated coordinate map is bounded by `max ‖L i‖`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L71-L94
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L71-L94

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem Malliavin.norm_fderiv_truncCoord_le (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖fderiv ℝ (truncCoord m L) x‖ ≤ ∑ i, ‖L i‖ := by sorry
