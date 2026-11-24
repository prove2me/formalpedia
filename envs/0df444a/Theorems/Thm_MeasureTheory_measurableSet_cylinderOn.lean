-- Prove2me | Theorems.Thm_MeasureTheory_measurableSet_cylinderOn
-- name    : MeasureTheory.measurableSet_cylinderOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:27.438027+00:00
-- url     : https://prove2.me/theorems/3c5a89aa-18ea-41f0-93d1-07ed12964531
-- title:
--   Measure Theory: measurable Set cylinder On
-- statement:
--   The Measure Theory construction uses the measurable Set cylinder On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L136-L137
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L136-L137

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

theorem MeasureTheory.measurableSet_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) : MeasurableSet (cylinderOn B v) := by sorry
