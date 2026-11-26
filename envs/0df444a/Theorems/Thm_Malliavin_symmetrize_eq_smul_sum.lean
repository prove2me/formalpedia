-- Prove2me | Theorems.Thm_Malliavin_symmetrize_eq_smul_sum
-- name    : Malliavin.symmetrize_eq_smul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:21.199869+00:00
-- url     : https://prove2.me/theorems/7bb07c0a-da92-490c-bdf4-ff31f45ba643
-- title:
--   Malliavin: symmetrize eq smul sum
-- statement:
--   `symmetrize n f` as a scalar multiple of a sum of coordinate-permuted copies of `f`
--   (the form used for the `Lᵖ` estimates).
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L91-L95
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L91-L95

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

theorem Malliavin.symmetrize_eq_smul_sum (n : ℕ) (f : (Fin n → T) → E) :
    symmetrize n f =
      ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f ∘ (fun t : Fin n → T => t ∘ σ) := by sorry
