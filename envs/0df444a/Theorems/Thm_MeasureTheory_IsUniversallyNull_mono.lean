-- Prove2me | Theorems.Thm_MeasureTheory_IsUniversallyNull_mono
-- name    : MeasureTheory.IsUniversallyNull.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:21:37.56186+00:00
-- url     : https://prove2.me/theorems/0a87be9b-0e7b-40f8-b6ba-4509d7473bcf
-- title:
--   Is Universally Null: mono
-- statement:
--   The Is Universally Null construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L49-L50
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L49-L50

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}

theorem MeasureTheory.IsUniversallyNull.mono (hB : IsUniversallyNull B) (h : A ⊆ B) : IsUniversallyNull A := by sorry
