-- Prove2me | Theorems.Thm_LatinQuarter_squarefree_coeff_zero_of_quotient_zero
-- name    : LatinQuarter.squarefree_coeff_zero_of_quotient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.773206+00:00
-- url     : https://prove2.me/theorems/79b0e9b8-2c0a-41be-9264-d34ef9db6994
-- title:
--   Latin Quarter: squarefree coeff zero of quotient zero
-- statement:
--   A zero polynomial in the bookkeeping ring has zero square-free
--   coefficients in the original polynomial ring.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L70-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L70-L74

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Definitions.Def_LeanPool_LatinQuarter_Tags
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
open MvPolynomial

theorem LatinQuarter.squarefree_coeff_zero_of_quotient_zero {κ : Type*}
    {p : MvPolynomial κ (ZMod 2)}
    (hp : Ideal.Quotient.mk (repeatedTagIdeal κ) p = 0)
    {d : κ →₀ ℕ} (hd : ∀ j, d j ≤ 1) : p.coeff d = 0 := by sorry
