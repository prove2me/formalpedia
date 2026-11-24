-- Prove2me | Theorems.Thm_MeasureTheory_determined_cylinderOn
-- name    : MeasureTheory.determined_cylinderOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:30.05789+00:00
-- url     : https://prove2.me/theorems/4faba446-5b76-4ca5-9a0d-967852ac447e
-- title:
--   Measure Theory: determined cylinder On
-- statement:
--   The Measure Theory construction uses the determined cylinder On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L139-L141
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L139-L141

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

theorem MeasureTheory.determined_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) {s : Set ℕ} (h : ↑B ⊆ s) :
    Determined s (cylinderOn B v) := by sorry
