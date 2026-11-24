-- Prove2me | Theorems.Thm_MeasureTheory_flip_apply_self
-- name    : MeasureTheory.flip_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:21:55.015924+00:00
-- url     : https://prove2.me/theorems/de8a5413-c183-499a-b4bc-1eac00f29c40
-- title:
--   Measure Theory: flip apply self
-- statement:
--   The Measure Theory construction uses the flip apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L38-L38
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L38-L38

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

theorem MeasureTheory.flip_apply_self (i : ℕ) (w : ℕ → Bool) : flip i w i = !w i := by sorry
