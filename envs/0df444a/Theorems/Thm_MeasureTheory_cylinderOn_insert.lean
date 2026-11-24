-- Prove2me | Theorems.Thm_MeasureTheory_cylinderOn_insert
-- name    : MeasureTheory.cylinderOn_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:24.068346+00:00
-- url     : https://prove2.me/theorems/3fbfe281-48fd-42b0-a8cb-91738c0de079
-- title:
--   Measure Theory: cylinder On insert
-- statement:
--   The Measure Theory construction uses the cylinder On insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L143-L146
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L143-L146

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

theorem MeasureTheory.cylinderOn_insert {B : Finset ℕ} {i : ℕ} (v : ℕ → Bool) :
    cylinderOn (insert i B) v = cylinderOn B v ∩ {w | w i = v i} := by sorry
