-- Prove2me | Theorems.Thm_Malliavin_symmetrize_of_isSymmetric
-- name    : Malliavin.symmetrize_of_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:22.001479+00:00
-- url     : https://prove2.me/theorems/badb7b0b-e855-403e-a593-0022dc98ce4a
-- title:
--   Malliavin: symmetrize of is Symmetric
-- statement:
--   The Malliavin construction uses the symmetrize of is Symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L141-L143
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L141-L143

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]

theorem Malliavin.symmetrize_of_isSymmetric {n : ℕ} {f : (Fin n → T) → E} (hf : IsSymmetric n f) :
    symmetrize n f = f := by sorry
