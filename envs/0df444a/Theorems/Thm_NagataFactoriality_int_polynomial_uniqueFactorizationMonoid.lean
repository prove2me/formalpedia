-- Prove2me | Theorems.Thm_NagataFactoriality_int_polynomial_uniqueFactorizationMonoid
-- name    : NagataFactoriality.int_polynomial_uniqueFactorizationMonoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:59.948185+00:00
-- url     : https://prove2.me/theorems/91d78e42-2853-43f0-bf3a-99217c1c4d7f
-- title:
--   Nagata Factoriality: int polynomial unique Factorization Monoid
-- statement:
--   The Nagata Factoriality construction uses the int polynomial unique Factorization Monoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Examples.lean#L12-L13
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Examples.lean#L12-L13

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples
set_option autoImplicit false
open NagataFactoriality
open Polynomial

theorem NagataFactoriality.int_polynomial_uniqueFactorizationMonoid : UniqueFactorizationMonoid ℤ[X] := by sorry
