-- Prove2me | Theorems.Thm_MeasureTheory_universallyNullSets_subset_nullSets
-- name    : MeasureTheory.universallyNullSets_subset_nullSets
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:28:19.472799+00:00
-- url     : https://prove2.me/theorems/1d449b47-2257-4794-9401-c5aeb2869e59
-- title:
--   Measure Theory: universally Null Sets subset null Sets
-- statement:
--   A universally null set is null for every finite measure that vanishes on singletons.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L61-L63
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L61-L63

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

theorem MeasureTheory.universallyNullSets_subset_nullSets (μ : Measure X) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : universallyNullSets X ⊆ μ.nullSets := by sorry
