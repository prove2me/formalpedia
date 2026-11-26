-- Prove2me | Theorems.Thm_Malliavin_measurableSet_sortedBy
-- name    : Malliavin.measurableSet_sortedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:27.065283+00:00
-- url     : https://prove2.me/theorems/1d8108e2-274b-4cde-94d0-7074625636de
-- title:
--   Malliavin: measurable Set sorted By
-- statement:
--   The Malliavin construction uses the measurable Set sorted By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L170-L172
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L170-L172

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]

theorem Malliavin.measurableSet_sortedBy (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (sortedBy T n σ) := by sorry
