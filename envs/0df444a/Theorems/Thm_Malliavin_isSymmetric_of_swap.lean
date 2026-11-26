-- Prove2me | Theorems.Thm_Malliavin_isSymmetric_of_swap
-- name    : Malliavin.isSymmetric_of_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:37.571523+00:00
-- url     : https://prove2.me/theorems/ff4f0bb1-7915-483b-808a-dc95532a04b5
-- title:
--   Malliavin: is Symmetric of swap
-- statement:
--   Symmetry only needs to be checked on transpositions (they generate `Equiv.Perm (Fin n)`).
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L58-L68
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L58-L68

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}

theorem Malliavin.isSymmetric_of_swap {n : ℕ} {f : (Fin n → T) → E}
    (h : ∀ x y : Fin n, x ≠ y → ∀ t : Fin n → T, f (t ∘ Equiv.swap x y) = f t) :
    IsSymmetric n f := by sorry
