-- Prove2me | Theorems.Thm_Malliavin_sortedBy_one
-- name    : Malliavin.sortedBy_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:56:25.520799+00:00
-- url     : https://prove2.me/theorems/67465552-b3b9-5132-bca4-742977702ffc
-- title:
--   Malliavin: sorted By one
-- statement:
--   The Malliavin construction uses the sorted By one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L97-L99
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L97-L99

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.sortedBy_one (n : ℕ) : sortedBy T n 1 = simplex T n := by sorry
