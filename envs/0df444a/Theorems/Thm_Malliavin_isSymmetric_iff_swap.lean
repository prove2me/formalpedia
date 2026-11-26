-- Prove2me | Theorems.Thm_Malliavin_isSymmetric_iff_swap
-- name    : Malliavin.isSymmetric_iff_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:13.877897+00:00
-- url     : https://prove2.me/theorems/d031f67b-58a5-4848-a8d3-a5effc557743
-- title:
--   Malliavin: is Symmetric iff swap
-- statement:
--   The Malliavin construction uses the is Symmetric iff swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L70-L72
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L70-L72

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}

theorem Malliavin.isSymmetric_iff_swap {n : ℕ} {f : (Fin n → T) → E} :
    IsSymmetric n f ↔ ∀ x y : Fin n, x ≠ y → ∀ t : Fin n → T, f (t ∘ Equiv.swap x y) = f t := by sorry
