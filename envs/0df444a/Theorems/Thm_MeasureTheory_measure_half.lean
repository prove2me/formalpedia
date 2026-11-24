-- Prove2me | Theorems.Thm_MeasureTheory_measure_half
-- name    : MeasureTheory.measure_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:24.357825+00:00
-- url     : https://prove2.me/theorems/468a404a-092b-40ab-8b03-a251bc25257c
-- title:
--   Measure Theory: measure half
-- statement:
--   The Measure Theory construction uses the measure half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L159-L162
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L159-L162

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

theorem MeasureTheory.measure_half {B : Set (ℕ → Bool)} (hB : MeasurableSet B) : μ (half μ B) = μ B / 2 := by sorry
