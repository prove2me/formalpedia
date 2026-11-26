-- Prove2me | Theorems.Thm_Malliavin_measurableSet_diagonal
-- name    : Malliavin.measurableSet_diagonal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:56:36.028635+00:00
-- url     : https://prove2.me/theorems/5975fc41-3a7b-4e0e-84f9-7a78ae9e8782
-- title:
--   Malliavin: measurable Set diagonal
-- statement:
--   The Malliavin construction uses the measurable Set diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L174-L183
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L174-L183

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

theorem Malliavin.measurableSet_diagonal (n : ℕ) : MeasurableSet (diagonal T n) := by sorry
