-- Prove2me | Theorems.Thm_Malliavin_symmetrize_comp_perm
-- name    : Malliavin.symmetrize_comp_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:39.051415+00:00
-- url     : https://prove2.me/theorems/d4f75bea-4a48-48d5-8d5c-b584e97af84b
-- title:
--   Malliavin: symmetrize comp perm
-- statement:
--   Precomposition with a permutation leaves `symmetrize n f` unchanged: reindex the sum over
--   `Equiv.Perm (Fin n)` by the bijection `σ ↦ τ * σ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L124-L128
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L124-L128

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

theorem Malliavin.symmetrize_comp_perm (n : ℕ) (f : (Fin n → T) → E) (τ : Equiv.Perm (Fin n))
    (t : Fin n → T) : symmetrize n f (t ∘ τ) = symmetrize n f t := by sorry
