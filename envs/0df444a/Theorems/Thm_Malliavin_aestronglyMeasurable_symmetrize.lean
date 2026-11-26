-- Prove2me | Theorems.Thm_Malliavin_aestronglyMeasurable_symmetrize
-- name    : Malliavin.aestronglyMeasurable_symmetrize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:55:28.456807+00:00
-- url     : https://prove2.me/theorems/c3d835b4-f0fd-4d25-b96f-8298ba6f79e2
-- title:
--   Malliavin: aestrongly Measurable symmetrize
-- statement:
--   The Malliavin construction uses the aestrongly Measurable symmetrize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L202-L209
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L202-L209

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}

theorem Malliavin.aestronglyMeasurable_symmetrize {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) :
    AEStronglyMeasurable (symmetrize n f) (Measure.pi fun _ : Fin n => μ) := by sorry
