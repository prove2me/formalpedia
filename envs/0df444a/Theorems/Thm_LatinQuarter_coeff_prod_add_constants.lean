-- Prove2me | Theorems.Thm_LatinQuarter_coeff_prod_add_constants
-- name    : LatinQuarter.coeff_prod_add_constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.818351+00:00
-- url     : https://prove2.me/theorems/60df2180-fe33-40e0-a799-0256a1029178
-- title:
--   Latin Quarter: coeff prod add constants
-- statement:
--   Adding constants to `m` individual tags does not change a coefficient
--   of total degree `m`. This also allows zero constants.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L78-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L78-L100

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

theorem LatinQuarter.coeff_prod_add_constants {ι κ : Type*} [Fintype ι]
    (f : ι → κ) (a : ι → ZMod 2) (d : κ →₀ ℕ)
    (hd : ∑ j ∈ d.support, d j = Fintype.card ι) :
    (∏ i, (X (f i) + C (a i))).coeff d = (∏ i, X (f i) : MvPolynomial κ (ZMod 2)).coeff d := by sorry
