-- Prove2me | Theorems.Thm_MeasureTheory_Determined_mono
-- name    : MeasureTheory.Determined.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:42.062731+00:00
-- url     : https://prove2.me/theorems/26131c24-9769-4826-b346-942abbfd06a6
-- title:
--   Determined: mono
-- statement:
--   The Determined construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L99-L100
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L99-L100

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
open MeasureTheory.Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}

theorem MeasureTheory.Determined.mono (h : Determined s E) (hst : s ⊆ t) : Determined t E := by sorry
