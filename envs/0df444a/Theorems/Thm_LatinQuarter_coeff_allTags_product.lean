-- Prove2me | Theorems.Thm_LatinQuarter_coeff_allTags_product
-- name    : LatinQuarter.coeff_allTags_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.036941+00:00
-- url     : https://prove2.me/theorems/18d5fad6-3414-4886-9a3b-3e634f477472
-- title:
--   Latin Quarter: coeff all Tags product
-- statement:
--   The Latin Quarter construction uses the coeff all Tags product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L122-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L122-L128

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

theorem LatinQuarter.coeff_allTags_product {κ : Type*} [Fintype κ] :
    (∏ j : κ, X j : MvPolynomial κ (ZMod 2)).coeff (allTagsExponent κ) = 1 := by sorry
