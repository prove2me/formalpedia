-- Prove2me | Theorems.Thm_Malliavin_isSymmetric_iff_symmetrize_eq
-- name    : Malliavin.isSymmetric_iff_symmetrize_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:15.059106+00:00
-- url     : https://prove2.me/theorems/503992ff-1307-4d76-a5b5-ba4daaf2396c
-- title:
--   Malliavin: is Symmetric iff symmetrize eq
-- statement:
--   The Malliavin construction uses the is Symmetric iff symmetrize eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L150-L152
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L150-L152

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

theorem Malliavin.isSymmetric_iff_symmetrize_eq {n : ℕ} {f : (Fin n → T) → E} :
    IsSymmetric n f ↔ symmetrize n f = f := by sorry
