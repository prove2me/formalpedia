-- Prove2me | Theorems.Thm_MeasureTheory_exists_isCompact_disjoint_of_null
-- name    : MeasureTheory.exists_isCompact_disjoint_of_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:18.696936+00:00
-- url     : https://prove2.me/theorems/794d5d45-b01e-4118-acd4-77eb0bf8f48a
-- title:
--   Measure Theory: exists is Compact disjoint of null
-- statement:
--   The complement of a null set contains a compact set of positive measure.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L198-L207
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L198-L207

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

theorem MeasureTheory.exists_isCompact_disjoint_of_null {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ K : Set (ℕ → Bool), IsCompact K ∧ cantorMeasure K ≠ 0 ∧ Disjoint K G := by sorry
