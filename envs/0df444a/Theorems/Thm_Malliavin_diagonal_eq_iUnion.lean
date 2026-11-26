-- Prove2me | Theorems.Thm_Malliavin_diagonal_eq_iUnion
-- name    : Malliavin.diagonal_eq_iUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:00.795998+00:00
-- url     : https://prove2.me/theorems/3e7bab90-4f68-5342-a000-b1f891e8d155
-- title:
--   Malliavin: diagonal eq i Union
-- statement:
--   The Malliavin construction uses the diagonal eq i Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L61-L74
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L61-L74

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}

theorem Malliavin.diagonal_eq_iUnion (n : ℕ) :
    diagonal T n = ⋃ (i : Fin n) (j : Fin n) (_ : i ≠ j), {t : Fin n → T | t i = t j} := by sorry
