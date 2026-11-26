-- Prove2me | Theorems.Thm_Malliavin_symmetrizeL_comp_symmetrizeL
-- name    : Malliavin.symmetrizeL_comp_symmetrizeL
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:56:05.153484+00:00
-- url     : https://prove2.me/theorems/7cd9a519-f79c-57bd-8cfd-8f53f1ba872a
-- title:
--   Malliavin: symmetrize L comp symmetrize L
-- statement:
--   The Malliavin construction uses the symmetrize L comp symmetrize L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L346-L348
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L346-L348

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

theorem Malliavin.symmetrizeL_comp_symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (symmetrizeL E (μ := μ) n p).comp (symmetrizeL E (μ := μ) n p) = symmetrizeL E (μ := μ) n p := by sorry
