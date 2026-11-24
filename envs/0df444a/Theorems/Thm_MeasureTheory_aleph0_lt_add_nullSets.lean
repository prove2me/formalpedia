-- Prove2me | Theorems.Thm_MeasureTheory_aleph0_lt_add_nullSets
-- name    : MeasureTheory.aleph0_lt_add_nullSets
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:28:27.807+00:00
-- url     : https://prove2.me/theorems/b619a5e2-914c-4729-b09b-2a641533d7b9
-- title:
--   Measure Theory: aleph0 lt add null Sets
-- statement:
--   The additivity of the null sets of a nonzero measure that vanishes on singletons is
--   uncountable.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L92-L101
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L92-L101

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

theorem MeasureTheory.aleph0_lt_add_nullSets (μ : Measure X) [NullSingletonClass μ] [NeZero μ] :
    ℵ₀ < add μ.nullSets := by sorry
