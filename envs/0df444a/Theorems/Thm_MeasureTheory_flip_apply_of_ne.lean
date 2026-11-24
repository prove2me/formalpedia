-- Prove2me | Theorems.Thm_MeasureTheory_flip_apply_of_ne
-- name    : MeasureTheory.flip_apply_of_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:28:30.540131+00:00
-- url     : https://prove2.me/theorems/e1455b72-795e-434c-8d44-5c63381674b4
-- title:
--   Measure Theory: flip apply of ne
-- statement:
--   The Measure Theory construction uses the flip apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L40-L41
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L40-L41

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

theorem MeasureTheory.flip_apply_of_ne {i j : ℕ} (h : j ≠ i) (w : ℕ → Bool) : flip i w j = w j := by sorry
