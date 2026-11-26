-- Prove2me | Theorems.Thm_Malliavin_isSymmetric_symmetrize
-- name    : Malliavin.isSymmetric_symmetrize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:17.976405+00:00
-- url     : https://prove2.me/theorems/929784ee-53fd-5817-9a2f-a4abac42ceab
-- title:
--   Malliavin: is Symmetric symmetrize
-- statement:
--   The Malliavin construction uses the is Symmetric symmetrize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L130-L131
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L130-L131

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

theorem Malliavin.isSymmetric_symmetrize (n : ℕ) (f : (Fin n → T) → E) : IsSymmetric n (symmetrize n f) := by sorry
