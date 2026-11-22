-- Prove2me | Theorems.Thm_LatinQuarter_tag_sq
-- name    : LatinQuarter.tag_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:25.662177+00:00
-- url     : https://prove2.me/theorems/a4b4b25b-845d-45f1-b21d-49029f11e81c
-- title:
--   Latin Quarter: tag sq
-- statement:
--   The Latin Quarter construction uses the tag sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L61-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Tags.lean#L61-L66

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

theorem LatinQuarter.tag_sq {κ : Type*} (j : κ) : tag j * tag j = 0 := by sorry
