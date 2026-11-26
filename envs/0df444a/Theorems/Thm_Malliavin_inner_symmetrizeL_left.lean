-- Prove2me | Theorems.Thm_Malliavin_inner_symmetrizeL_left
-- name    : Malliavin.inner_symmetrizeL_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:43.451309+00:00
-- url     : https://prove2.me/theorems/8edc41d0-e265-485b-bbf1-a141a44ffef4
-- title:
--   Malliavin: inner symmetrize L left
-- statement:
--   `symmetrizeL` is self-adjoint on `L²`: together with idempotence this makes it the orthogonal
--   projection onto the a.e.-symmetric functions.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L420-L426
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L420-L426

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

theorem Malliavin.inner_symmetrizeL_left (n : ℕ) (f g : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (symmetrizeL E (μ := μ) n 2 f) g = inner ℝ f (symmetrizeL E (μ := μ) n 2 g) := by sorry
