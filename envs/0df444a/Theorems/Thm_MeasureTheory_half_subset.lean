-- Prove2me | Theorems.Thm_MeasureTheory_half_subset
-- name    : MeasureTheory.half_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:25:46.372817+00:00
-- url     : https://prove2.me/theorems/f2330516-850d-4b5f-ab40-cf91dbb7e15f
-- title:
--   Measure Theory: half subset
-- statement:
--   The Measure Theory construction uses the half subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L147-L151
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L147-L151

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

theorem MeasureTheory.half_subset (B : Set (ℕ → Bool)) : half μ B ⊆ B := by sorry
