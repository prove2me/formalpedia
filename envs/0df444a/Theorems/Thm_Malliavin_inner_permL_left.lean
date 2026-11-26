-- Prove2me | Theorems.Thm_Malliavin_inner_permL_left
-- name    : Malliavin.inner_permL_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:36.190249+00:00
-- url     : https://prove2.me/theorems/f79d5ea2-5c5b-40c9-a6df-67af15922429
-- title:
--   Malliavin: inner perm L left
-- statement:
--   The Malliavin construction uses the inner perm L left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L393-L416
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L393-L416

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

theorem Malliavin.inner_permL_left (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (permL E (μ := μ) n 2 σ f) g = inner ℝ f (permL E (μ := μ) n 2 σ⁻¹ g) := by sorry
