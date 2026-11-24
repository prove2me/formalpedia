-- Prove2me | Theorems.Thm_MeasureTheory_measurePreserving_flip
-- name    : MeasureTheory.measurePreserving_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:20.070186+00:00
-- url     : https://prove2.me/theorems/7034a1a5-8b42-4de9-be5d-53a77d06ca2c
-- title:
--   Measure Theory: measure Preserving flip
-- statement:
--   Flipping one coordinate preserves the coin-tossing measure.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L61-L74
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L61-L74

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

theorem MeasureTheory.measurePreserving_flip (i : ℕ) :
    MeasurePreserving (flip i) cantorMeasure cantorMeasure := by sorry
