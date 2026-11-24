-- Prove2me | Theorems.Thm_MeasureTheory_uniformBool_map_not
-- name    : MeasureTheory.uniformBool_map_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:22.249425+00:00
-- url     : https://prove2.me/theorems/07e61e91-6e04-4c74-986c-29ddbd6bbe11
-- title:
--   Measure Theory: uniform Bool map not
-- statement:
--   The Measure Theory construction uses the uniform Bool map not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L48-L58
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L48-L58

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

theorem MeasureTheory.uniformBool_map_not :
    (PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ !b) =
      (PMF.uniformOfFintype Bool).toMeasure := by sorry
