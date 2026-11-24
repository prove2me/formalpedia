-- Prove2me | Theorems.Thm_MeasureTheory_measurable_split
-- name    : MeasureTheory.measurable_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:26:17.090806+00:00
-- url     : https://prove2.me/theorems/eb72dba2-ca75-4511-9240-9f0eae2cffda
-- title:
--   Measure Theory: measurable split
-- statement:
--   The Measure Theory construction uses the measurable split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L267-L272
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L267-L272

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem MeasureTheory.measurable_split : Measurable (split μ) := by sorry
