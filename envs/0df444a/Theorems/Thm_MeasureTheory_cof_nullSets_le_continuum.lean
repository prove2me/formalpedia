-- Prove2me | Theorems.Thm_MeasureTheory_cof_nullSets_le_continuum
-- name    : MeasureTheory.cof_nullSets_le_continuum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:28:26.161451+00:00
-- url     : https://prove2.me/theorems/7c9e30bf-bd4d-4b8a-b53f-eb02bca16f97
-- title:
--   Measure Theory: cof null Sets le continuum
-- statement:
--   In a countably generated measurable space the null sets of a measure have a cofinal
--   subfamily of size at most the continuum: the measurable null sets.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L118-L127
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L118-L127

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

theorem MeasureTheory.cof_nullSets_le_continuum [MeasurableSpace.CountablyGenerated X] (μ : Measure X) :
    cof μ.nullSets ≤ 𝔠 := by sorry
