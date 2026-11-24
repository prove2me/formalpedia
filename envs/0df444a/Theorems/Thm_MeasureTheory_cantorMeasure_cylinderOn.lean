-- Prove2me | Theorems.Thm_MeasureTheory_cantorMeasure_cylinderOn
-- name    : MeasureTheory.cantorMeasure_cylinderOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:22:33.884458+00:00
-- url     : https://prove2.me/theorems/9220d988-e8ca-4c53-a17b-372b808535d3
-- title:
--   Measure Theory: cantor Measure cylinder On
-- statement:
--   A cylinder on the finite set `B` has measure `2⁻¹ ^ B.card`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L188-L190
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L188-L190

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

theorem MeasureTheory.cantorMeasure_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) :
    cantorMeasure (cylinderOn B v) = 2⁻¹ ^ B.card := by sorry
