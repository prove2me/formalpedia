-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_fix_eq_lmarginal
-- name    : GaussianPerimeter.VolumeComparison.lintegral_fix_eq_lmarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:20:45.146553+00:00
-- url     : https://prove2.me/theorems/6a3947fa-b0e8-48ef-bc93-41c6de9f7e47
-- title:
--   Volume Comparison: lintegral fix eq lmarginal
-- statement:
--   The Volume Comparison construction uses the lintegral fix eq lmarginal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L559-L572
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L559-L572

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise

theorem GaussianPerimeter.VolumeComparison.lintegral_fix_eq_lmarginal {d : ℕ}
    (F : (Fin (d + 2) → ℝ) → ENNReal) (x1 : Fin (d + 1) → ℝ)
    : ∫⁻ y : Fin 1 → ℝ, (fix F x1) y = (∫⋯∫⁻_{⟨d+1, by simp⟩}, F) (append x1 default) := by sorry
