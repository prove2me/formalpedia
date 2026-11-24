-- Prove2me | Theorems.Thm_MomentComparison_lensAngle_eq_four_arctan
-- name    : MomentComparison.lensAngle_eq_four_arctan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:28.073813+00:00
-- url     : https://prove2.me/theorems/72a3b2ee-86ab-4152-84a0-b72a34918d5f
-- title:
--   Moment Comparison: lens Angle eq four arctan
-- statement:
--   The angle in equation (191) in terms of the slope of the lens at its vertex.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/LensAngle.lean#L12-L38
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/LensAngle.lean#L12-L38

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_LensAngle
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.lensAngle_eq_four_arctan {p : ℝ} (hp : 2 < p) :
    2 * Real.arcsin (2 * Real.sqrt (p - 1) / p) =
      4 * Real.arctan (Real.sqrt (p - 1))⁻¹ := by sorry
