-- Prove2me | Theorems.Thm_Malliavin_symmetrize_apply_of_forall
-- name    : Malliavin.symmetrize_apply_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:12.650156+00:00
-- url     : https://prove2.me/theorems/835af587-1973-5929-b37b-5658a2fe94d6
-- title:
--   Malliavin: symmetrize apply of forall
-- statement:
--   Pointwise version of `symmetrize_of_isSymmetric`: at a point `t` where all permuted values
--   agree, the average is just `f t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L135-L139
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L135-L139

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

theorem Malliavin.symmetrize_apply_of_forall {n : ℕ} {f : (Fin n → T) → E} {t : Fin n → T}
    (h : ∀ σ : Equiv.Perm (Fin n), f (t ∘ σ) = f t) : symmetrize n f t = f t := by sorry
