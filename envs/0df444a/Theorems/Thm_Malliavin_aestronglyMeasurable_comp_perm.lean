-- Prove2me | Theorems.Thm_Malliavin_aestronglyMeasurable_comp_perm
-- name    : Malliavin.aestronglyMeasurable_comp_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:48.012419+00:00
-- url     : https://prove2.me/theorems/dff004c3-e32c-44a1-8d7b-e58c9496ebe5
-- title:
--   Malliavin: aestrongly Measurable comp perm
-- statement:
--   The Malliavin construction uses the aestrongly Measurable comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L197-L200
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L197-L200

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
omit [NormedSpace ℝ E]

theorem Malliavin.aestronglyMeasurable_comp_perm {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) (σ : Equiv.Perm (Fin n)) :
    AEStronglyMeasurable (f ∘ fun t : Fin n → T => t ∘ σ) (Measure.pi fun _ : Fin n => μ) := by sorry
