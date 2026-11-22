-- Prove2me | Theorems.Thm_LatinQuarter_allTagsExponent_support
-- name    : LatinQuarter.allTagsExponent_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:27.722288+00:00
-- url     : https://prove2.me/theorems/d52df8ab-3c80-45b9-bb3a-ab5ba6ef1671
-- title:
--   Latin Quarter: all Tags Exponent support
-- statement:
--   The Latin Quarter construction uses the all Tags Exponent support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L111-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L111-L115

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

theorem LatinQuarter.allTagsExponent_support {κ : Type*} [Fintype κ] :
    (allTagsExponent κ).support = Finset.univ := by sorry
