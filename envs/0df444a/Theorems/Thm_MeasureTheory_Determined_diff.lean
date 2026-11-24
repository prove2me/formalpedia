-- Prove2me | Theorems.Thm_MeasureTheory_Determined_diff
-- name    : MeasureTheory.Determined.diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:08.465168+00:00
-- url     : https://prove2.me/theorems/67ef8729-6da7-4e58-bc24-99d2ad584c63
-- title:
--   Determined: diff
-- statement:
--   The Determined construction uses the diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L110-L111
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L110-L111

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

theorem MeasureTheory.Determined.diff (hE : Determined s E) (hF : Determined s F) : Determined s (E \ F) := by sorry
