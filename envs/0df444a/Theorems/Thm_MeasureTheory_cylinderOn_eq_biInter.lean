-- Prove2me | Theorems.Thm_MeasureTheory_cylinderOn_eq_biInter
-- name    : MeasureTheory.cylinderOn_eq_biInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:29:19.840364+00:00
-- url     : https://prove2.me/theorems/4970f997-1234-4e8a-98c0-6c95646709c0
-- title:
--   Measure Theory: cylinder On eq bi Inter
-- statement:
--   The Measure Theory construction uses the cylinder On eq bi Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L126-L129
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L126-L129

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

theorem MeasureTheory.cylinderOn_eq_biInter (B : Finset ℕ) (v : ℕ → Bool) :
    cylinderOn B v = ⋂ i ∈ B, (fun w : ℕ → Bool ↦ w i) ⁻¹' {v i} := by sorry
