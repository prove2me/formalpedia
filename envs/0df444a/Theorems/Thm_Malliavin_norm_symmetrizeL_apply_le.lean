-- Prove2me | Theorems.Thm_Malliavin_norm_symmetrizeL_apply_le
-- name    : Malliavin.norm_symmetrizeL_apply_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:08.279644+00:00
-- url     : https://prove2.me/theorems/d138c865-37d7-540b-8e71-b29ab48f7c90
-- title:
--   Malliavin: norm symmetrize L apply le
-- statement:
--   The Malliavin construction uses the norm symmetrize L apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L329-L334
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L329-L334

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

theorem Malliavin.norm_symmetrizeL_apply_le (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ‖symmetrizeL E (μ := μ) n p f‖ ≤ ‖f‖ := by sorry
