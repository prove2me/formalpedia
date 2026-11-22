-- Prove2me | Theorems.Thm_LatinQuarter_product_eq_zero_of_repeated_square_zero
-- name    : LatinQuarter.product_eq_zero_of_repeated_square_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.715791+00:00
-- url     : https://prove2.me/theorems/0dafc5bb-b4a3-4706-a09f-99d80ab751df
-- title:
--   Latin Quarter: product eq zero of repeated square zero
-- statement:
--   The Latin Quarter construction uses the product eq zero of repeated square zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean#L21-L29
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean#L21-L29

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

theorem LatinQuarter.product_eq_zero_of_repeated_square_zero
    {ι : Type*} [Fintype ι] (f : ι → R)
    {a b : ι} (hab : a ≠ b) (heq : f a = f b)
    (hsq : f a * f a = 0) : ∏ i, f i = 0 := by sorry
