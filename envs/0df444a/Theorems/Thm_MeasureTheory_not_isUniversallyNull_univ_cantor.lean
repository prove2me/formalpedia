-- Prove2me | Theorems.Thm_MeasureTheory_not_isUniversallyNull_univ_cantor
-- name    : MeasureTheory.not_isUniversallyNull_univ_cantor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:21:45.256907+00:00
-- url     : https://prove2.me/theorems/75eda74b-807a-4130-9e5d-aea77c9ce9fb
-- title:
--   Measure Theory: not is Universally Null univ cantor
-- statement:
--   The Cantor space is not universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L85-L86
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L85-L86

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

theorem MeasureTheory.not_isUniversallyNull_univ_cantor : ¬ IsUniversallyNull (Set.univ : Set (ℕ → Bool)) := by sorry
