-- Prove2me | Theorems.Thm_NagataFactoriality_iterated_polynomial_uniqueFactorizationMonoid
-- name    : NagataFactoriality.iterated_polynomial_uniqueFactorizationMonoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:01.248688+00:00
-- url     : https://prove2.me/theorems/2b696a0c-49f5-5000-be7f-9625d50b025b
-- title:
--   Nagata Factoriality: iterated polynomial unique Factorization Monoid
-- statement:
--   The Nagata Factoriality construction uses the iterated polynomial unique Factorization Monoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Examples.lean#L19-L21
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Examples.lean#L19-L21

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples
set_option autoImplicit false
open NagataFactoriality
open Polynomial

theorem NagataFactoriality.iterated_polynomial_uniqueFactorizationMonoid (k : Type*) [Field k] :
    UniqueFactorizationMonoid (Polynomial (Polynomial k)) := by sorry
