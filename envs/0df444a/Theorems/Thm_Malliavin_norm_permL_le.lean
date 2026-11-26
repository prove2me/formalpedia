-- Prove2me | Theorems.Thm_Malliavin_norm_permL_le
-- name    : Malliavin.norm_permL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:14.693718+00:00
-- url     : https://prove2.me/theorems/af61e3a6-e11b-543b-b311-938d673c5477
-- title:
--   Malliavin: norm perm L le
-- statement:
--   The Malliavin construction uses the norm perm L le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L284-L286
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L284-L286

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

theorem Malliavin.norm_permL_le (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n)) :
    ‖permL E (μ := μ) n p σ‖ ≤ 1 := by sorry
