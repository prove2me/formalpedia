-- Prove2me | Theorems.Thm_MeasureTheory_aleph0_lt_add_universallyNullSets
-- name    : MeasureTheory.aleph0_lt_add_universallyNullSets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:28:27.544046+00:00
-- url     : https://prove2.me/theorems/c2949d11-7e4a-4a68-b15e-16deeb7923df
-- title:
--   Measure Theory: aleph0 lt add universally Null Sets
-- statement:
--   The additivity of the universally null sets is uncountable when the whole space is not
--   universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L105-L114
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L105-L114

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

theorem MeasureTheory.aleph0_lt_add_universallyNullSets (h : ¬ IsUniversallyNull (Set.univ : Set X)) :
    ℵ₀ < add (universallyNullSets X) := by sorry
