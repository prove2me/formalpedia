-- Prove2me | Theorems.Thm_Malliavin_contDiff_truncCoord
-- name    : Malliavin.contDiff_truncCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:33.475128+00:00
-- url     : https://prove2.me/theorems/c4a359d1-0779-4ab7-be4b-a67177d3736c
-- title:
--   Malliavin: cont Diff trunc Coord
-- statement:
--   The Malliavin construction uses the cont Diff trunc Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L52-L54
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L52-L54

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem Malliavin.contDiff_truncCoord (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) :
    ContDiff ℝ 1 (truncCoord m L) := by sorry
