-- Prove2me | Theorems.Thm_Malliavin_symmetrizeL_symmetrizeL
-- name    : Malliavin.symmetrizeL_symmetrizeL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:04.154038+00:00
-- url     : https://prove2.me/theorems/4d268334-d57b-59c4-96f7-435b459e191f
-- title:
--   Malliavin: symmetrize L symmetrize L
-- statement:
--   `symmetrizeL` is idempotent.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L337-L344
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L337-L344

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

theorem Malliavin.symmetrizeL_symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p (symmetrizeL E (μ := μ) n p f) = symmetrizeL E (μ := μ) n p f := by sorry
