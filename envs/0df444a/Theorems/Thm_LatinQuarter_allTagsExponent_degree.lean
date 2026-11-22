-- Prove2me | Theorems.Thm_LatinQuarter_allTagsExponent_degree
-- name    : LatinQuarter.allTagsExponent_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:33.417251+00:00
-- url     : https://prove2.me/theorems/27541866-893e-415e-b722-cd2e065e301d
-- title:
--   Latin Quarter: all Tags Exponent degree
-- statement:
--   The Latin Quarter construction uses the all Tags Exponent degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L117-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L117-L120

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

theorem LatinQuarter.allTagsExponent_degree {κ : Type*} [Fintype κ] :
    ∑ j ∈ (allTagsExponent κ).support, allTagsExponent κ j = Fintype.card κ := by sorry
