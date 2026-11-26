-- Prove2me | Theorems.Thm_Malliavin_IsSmoothBounded_comp_continuousLinearMap
-- name    : Malliavin.IsSmoothBounded.comp_continuousLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:36.75068+00:00
-- url     : https://prove2.me/theorems/4fd5e7dd-cfc2-4e92-a4af-1ed6e22669f3
-- title:
--   Is Smooth Bounded: comp continuous Linear Map
-- statement:
--   Precomposition by a continuous linear map preserves the class of smooth bounded
--   functionals.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L31-L41
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L31-L41

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem Malliavin.IsSmoothBounded.comp_continuousLinearMap
    {f : F → ℝ} (hf : IsSmoothBounded f) (L : E →L[ℝ] F) :
    IsSmoothBounded (f ∘ L) := by sorry
