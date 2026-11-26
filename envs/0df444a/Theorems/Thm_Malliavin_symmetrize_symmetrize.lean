-- Prove2me | Theorems.Thm_Malliavin_symmetrize_symmetrize
-- name    : Malliavin.symmetrize_symmetrize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:52.033934+00:00
-- url     : https://prove2.me/theorems/6a74c4b0-4c75-4092-a9c7-67bf6f7f1fe3
-- title:
--   Malliavin: symmetrize symmetrize
-- statement:
--   Symmetrization is idempotent.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L146-L148
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L146-L148

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

theorem Malliavin.symmetrize_symmetrize (n : ℕ) (f : (Fin n → T) → E) :
    symmetrize n (symmetrize n f) = symmetrize n f := by sorry
