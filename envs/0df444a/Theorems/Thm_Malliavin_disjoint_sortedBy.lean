-- Prove2me | Theorems.Thm_Malliavin_disjoint_sortedBy
-- name    : Malliavin.disjoint_sortedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:20.92435+00:00
-- url     : https://prove2.me/theorems/f001f81c-4664-425f-9ebc-589107649610
-- title:
--   Malliavin: disjoint sorted By
-- statement:
--   The Malliavin construction uses the disjoint sorted By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L123-L127
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L123-L127

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.disjoint_sortedBy {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : σ ≠ τ) :
    Disjoint (sortedBy T n σ) (sortedBy T n τ) := by sorry
