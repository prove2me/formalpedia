-- Prove2me | Theorems.Thm_MeasureTheory_isClopen_cylinderOn
-- name    : MeasureTheory.isClopen_cylinderOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:29.309801+00:00
-- url     : https://prove2.me/theorems/04ff3495-0dea-4322-877c-f2d8a311ee76
-- title:
--   Measure Theory: is Clopen cylinder On
-- statement:
--   The Measure Theory construction uses the is Clopen cylinder On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L131-L134
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L131-L134

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

theorem MeasureTheory.isClopen_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) : IsClopen (cylinderOn B v) := by sorry
