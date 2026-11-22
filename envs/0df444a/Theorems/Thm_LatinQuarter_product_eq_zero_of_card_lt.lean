-- Prove2me | Theorems.Thm_LatinQuarter_product_eq_zero_of_card_lt
-- name    : LatinQuarter.product_eq_zero_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:29.823946+00:00
-- url     : https://prove2.me/theorems/09a4b6d5-dd7b-46f7-827c-aca6a391c035
-- title:
--   Latin Quarter: product eq zero of card lt
-- statement:
--   The Latin Quarter construction uses the product eq zero of card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean#L31-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean#L31-L44

module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Pointwise
variable {R : Type*} [CommRing R]

theorem LatinQuarter.product_eq_zero_of_card_lt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : κ → R) (hz : ∀ j, z j * z j = 0)
    (f : ι → κ) (hcard : Fintype.card κ < Fintype.card ι) :
    ∏ i, z (f i) = 0 := by sorry
