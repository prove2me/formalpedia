-- Prove2me | Theorems.Thm_Malliavin_measurableSet_simplex
-- name    : Malliavin.measurableSet_simplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:11.454651+00:00
-- url     : https://prove2.me/theorems/b7c2502a-0da7-506c-8c16-5bf5c880ec96
-- title:
--   Malliavin: measurable Set simplex
-- statement:
--   The Malliavin construction uses the measurable Set simplex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L160-L168
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L160-L168

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

theorem Malliavin.measurableSet_simplex (n : ℕ) : MeasurableSet (simplex T n) := by sorry
