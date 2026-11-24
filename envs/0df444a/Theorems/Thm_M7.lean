-- Prove2me | Theorems.Thm_M7
-- name    : M7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:14.979188+00:00
-- url     : https://prove2.me/theorems/d2820743-8563-431f-86a0-9177c24cbde7
-- title:
--   M7: M7
-- statement:
--   The Minkowski bound for a seventh-cyclotomic number field is `4`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean#L50-L56

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
set_option autoImplicit false
@[expose] public section
public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
variable [IsCyclotomicExtension {7} ℚ K]

theorem M7 : ⌊(M K)⌋₊ = 4 := by sorry
