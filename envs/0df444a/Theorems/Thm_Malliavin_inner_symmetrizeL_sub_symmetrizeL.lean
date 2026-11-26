-- Prove2me | Theorems.Thm_Malliavin_inner_symmetrizeL_sub_symmetrizeL
-- name    : Malliavin.inner_symmetrizeL_sub_symmetrizeL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:40.799935+00:00
-- url     : https://prove2.me/theorems/23a83168-b8f5-4902-9719-07dfd046456a
-- title:
--   Malliavin: inner symmetrize L sub symmetrize L
-- statement:
--   `f - symmetrizeL f` is orthogonal to `symmetrizeL f`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L429-L432
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L429-L432

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Malliavin.inner_symmetrizeL_sub_symmetrizeL (n : ℕ) (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (symmetrizeL E (μ := μ) n 2 f) (f - symmetrizeL E (μ := μ) n 2 f) = 0 := by sorry
