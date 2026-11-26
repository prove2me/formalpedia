-- Prove2me | Theorems.Thm_Malliavin_iUnion_sortedBy_eq
-- name    : Malliavin.iUnion_sortedBy_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:22.82954+00:00
-- url     : https://prove2.me/theorems/50bc8d07-2ec8-4779-a221-874dd6346f8d
-- title:
--   Malliavin: i Union sorted By eq
-- statement:
--   The tiles `sortedBy σ` cover exactly the injective tuples.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L130-L139
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L130-L139

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.iUnion_sortedBy_eq (n : ℕ) :
    ⋃ σ : Equiv.Perm (Fin n), sortedBy T n σ = (diagonal T n)ᶜ := by sorry
