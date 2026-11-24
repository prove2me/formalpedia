-- Prove2me | Theorems.Thm_MeasureTheory_Determined_compl
-- name    : MeasureTheory.Determined.compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:52.409259+00:00
-- url     : https://prove2.me/theorems/8cccd992-5359-4632-9787-199e194792df
-- title:
--   Determined: compl
-- statement:
--   The Determined construction uses the compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L107-L108
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L107-L108

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
open MeasureTheory.Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}

theorem MeasureTheory.Determined.compl (hE : Determined s E) : Determined s Eᶜ := by sorry
