-- Prove2me | Theorems.Thm_MeasureTheory_generateFrom_initialCylinders
-- name    : MeasureTheory.generateFrom_initialCylinders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:25:19.059174+00:00
-- url     : https://prove2.me/theorems/c5065b21-4b38-4b86-9b7c-215a801072e0
-- title:
--   Measure Theory: generate From initial Cylinders
-- statement:
--   The initial cylinders generate the σ-algebra of the Cantor space.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/InitialCylinder.lean#L42-L73
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/InitialCylinder.lean#L42-L73

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_InitialCylinder
set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory

theorem MeasureTheory.generateFrom_initialCylinders :
    (inferInstance : MeasurableSpace (ℕ → Bool)) =
      MeasurableSpace.generateFrom initialCylinders := by sorry
