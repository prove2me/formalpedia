-- Prove2me | Theorems.Thm_Malliavin_isSmoothBounded_comp_truncCoord
-- name    : Malliavin.isSmoothBounded_comp_truncCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:24:59.065837+00:00
-- url     : https://prove2.me/theorems/c4ea54ec-4697-5b4a-9029-5e6de14610b4
-- title:
--   Malliavin: is Smooth Bounded comp trunc Coord
-- statement:
--   `f ∘ truncCoord` is smooth bounded for every `C¹` function `f`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L97-L117
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L97-L117

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem Malliavin.isSmoothBounded_comp_truncCoord {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (m : ℕ) (L : Fin n → StrongDual ℝ W) :
    IsSmoothBounded (fun x ↦ f (truncCoord m L x)) := by sorry
