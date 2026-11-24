-- Prove2me | Theorems.Thm_MeasureTheory_isUniversallyNull_sUnion
-- name    : MeasureTheory.isUniversallyNull_sUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:28:18.65322+00:00
-- url     : https://prove2.me/theorems/b0c4ab2b-6347-455e-a137-6a275666c83b
-- title:
--   Measure Theory: is Universally Null s Union
-- statement:
--   A countable union of universally null sets is universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L56-L58
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L56-L58

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

theorem MeasureTheory.isUniversallyNull_sUnion {𝒜 : Set (Set X)} (h𝒜 : 𝒜.Countable)
    (h : ∀ A ∈ 𝒜, IsUniversallyNull A) : IsUniversallyNull (⋃₀ 𝒜) := by sorry
