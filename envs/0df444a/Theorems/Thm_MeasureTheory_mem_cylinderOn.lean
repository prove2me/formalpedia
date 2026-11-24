-- Prove2me | Theorems.Thm_MeasureTheory_mem_cylinderOn
-- name    : MeasureTheory.mem_cylinderOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:00.370566+00:00
-- url     : https://prove2.me/theorems/bfd47f1c-e67a-4e29-b532-2b2d0fd8dbaa
-- title:
--   Measure Theory: mem cylinder On
-- statement:
--   The Measure Theory construction uses the mem cylinder On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L123-L124
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L123-L124

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

theorem MeasureTheory.mem_cylinderOn {B : Finset ℕ} {v w : ℕ → Bool} : w ∈ cylinderOn B v ↔ ∀ i ∈ B, w i = v i := by sorry
