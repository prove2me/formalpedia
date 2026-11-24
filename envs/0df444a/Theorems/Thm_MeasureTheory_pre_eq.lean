-- Prove2me | Theorems.Thm_MeasureTheory_pre_eq
-- name    : MeasureTheory.pre_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:42.398368+00:00
-- url     : https://prove2.me/theorems/8196e62a-2b16-4621-aa80-3a30ff35530e
-- title:
--   Measure Theory: pre eq
-- statement:
--   The Measure Theory construction uses the pre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L220-L223
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L220-L223

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

theorem MeasureTheory.pre_eq (x : ℕ → Bool) (n : ℕ) : pre μ x n = revPrefix (split μ x) n := by sorry
