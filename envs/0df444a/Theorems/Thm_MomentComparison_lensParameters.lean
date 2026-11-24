-- Prove2me | Theorems.Thm_MomentComparison_lensParameters
-- name    : MomentComparison.lensParameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:41.16547+00:00
-- url     : https://prove2.me/theorems/e10419a9-ef45-4179-842f-410dd8c08784
-- title:
--   Moment Comparison: lens Parameters
-- statement:
--   The aperture and boundary slope of the complex hypercontractivity lens.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/LensAngle.lean#L41-L78
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/LensAngle.lean#L41-L78

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_LensAngle
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.lensParameters {p : ℝ} (hp : 2 < p) :
    let r := Real.sqrt (p - 1)
    let β := (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) / Real.pi
    let k := (p - 2) / (2 * r)
    0 < r ∧ r ^ 2 = p - 1 ∧ 0 < β ∧ β < 2 ∧
      Real.cos (β * Real.pi / 2) + k * Real.sin (β * Real.pi / 2) = 0 := by sorry
