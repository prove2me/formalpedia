-- Prove2me | Theorems.Thm_Malliavin_memLp_symmetrize
-- name    : Malliavin.memLp_symmetrize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:55:33.380626+00:00
-- url     : https://prove2.me/theorems/c95d6a73-affd-5fa8-909b-7deb91e12e1a
-- title:
--   Malliavin: mem Lp symmetrize
-- statement:
--   The Malliavin construction uses the mem Lp symmetrize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L235-L240
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L235-L240

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

theorem Malliavin.memLp_symmetrize {n : ℕ} {f : (Fin n → T) → E} {p : ℝ≥0∞}
    (hf : MemLp f p (Measure.pi fun _ : Fin n => μ)) :
    MemLp (symmetrize n f) p (Measure.pi fun _ : Fin n => μ) := by sorry
