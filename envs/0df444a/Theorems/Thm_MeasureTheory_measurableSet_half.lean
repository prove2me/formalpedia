-- Prove2me | Theorems.Thm_MeasureTheory_measurableSet_half
-- name    : MeasureTheory.measurableSet_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:25:37.929049+00:00
-- url     : https://prove2.me/theorems/b20af3bc-532c-4672-975d-4ef6e1504cd9
-- title:
--   Measure Theory: measurable Set half
-- statement:
--   The Measure Theory construction uses the measurable Set half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L153-L157
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L153-L157

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

theorem MeasureTheory.measurableSet_half (B : Set (ℕ → Bool)) : MeasurableSet (half μ B) := by sorry
