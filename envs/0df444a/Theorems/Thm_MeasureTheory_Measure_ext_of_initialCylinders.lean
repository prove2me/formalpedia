-- Prove2me | Theorems.Thm_MeasureTheory_Measure_ext_of_initialCylinders
-- name    : MeasureTheory.Measure.ext_of_initialCylinders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:25:23.865827+00:00
-- url     : https://prove2.me/theorems/d1f86858-78c7-4e01-927d-344adf2279e8
-- title:
--   Measure: ext of initial Cylinders
-- statement:
--   Two finite measures on the Cantor space that agree on the initial cylinders are equal.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/InitialCylinder.lean#L76-L80
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/InitialCylinder.lean#L76-L80

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_InitialCylinder
set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory

theorem MeasureTheory.Measure.ext_of_initialCylinders {μ ν : Measure (ℕ → Bool)} [IsFiniteMeasure μ]
    (h : ∀ (n : ℕ) (v : ℕ → Bool),
      μ (cylinderOn (Finset.range n) v) = ν (cylinderOn (Finset.range n) v)) : μ = ν := by sorry
