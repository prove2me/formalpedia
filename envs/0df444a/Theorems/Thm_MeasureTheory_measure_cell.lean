-- Prove2me | Theorems.Thm_MeasureTheory_measure_cell
-- name    : MeasureTheory.measure_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:40.927351+00:00
-- url     : https://prove2.me/theorems/6243985a-b2bf-452e-a61d-4dcbe07912b1
-- title:
--   Measure Theory: measure cell
-- statement:
--   The Measure Theory construction uses the measure cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L177-L188
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L177-L188

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_Determined_univ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem MeasureTheory.measure_cell (s : List Bool) : μ (cell μ s) = μ univ * 2⁻¹ ^ s.length := by sorry
