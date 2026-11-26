-- Prove2me | Theorems.Thm_Malliavin_IsSymmetric_comp_left
-- name    : Malliavin.IsSymmetric.comp_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:56.399808+00:00
-- url     : https://prove2.me/theorems/4a1dc4f2-ea26-5c0f-803a-0eb14f8c67aa
-- title:
--   Is Symmetric: comp left
-- statement:
--   Post-composition preserves symmetry.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L50-L52
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L50-L52

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}

theorem Malliavin.IsSymmetric.comp_left {n : ℕ} {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    {F : Type*} (φ : E → F) : IsSymmetric n (φ ∘ g) := by sorry
