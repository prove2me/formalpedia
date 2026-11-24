-- Prove2me | Theorems.Thm_MeasureTheory_Determined_mem_iff
-- name    : MeasureTheory.Determined.mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:28:56.279332+00:00
-- url     : https://prove2.me/theorems/44523209-d1e4-4cc4-bce3-0bb59cbf1e87
-- title:
--   Determined: mem iff
-- statement:
--   The Determined construction uses the mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L95-L97
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L95-L97

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

theorem MeasureTheory.Determined.mem_iff (h : Determined s E) {w w' : ℕ → Bool} (hw : ∀ i ∈ s, w i = w' i) :
    w ∈ E ↔ w' ∈ E := by sorry
