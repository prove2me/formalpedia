-- Prove2me | Theorems.Thm_NagataFactoriality_int_uniqueFactorizationMonoid
-- name    : NagataFactoriality.int_uniqueFactorizationMonoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:59.401158+00:00
-- url     : https://prove2.me/theorems/584f8286-c1d8-4455-bd87-f711593ba0d1
-- title:
--   Nagata Factoriality: int unique Factorization Monoid
-- statement:
--   The Nagata Factoriality construction uses the int unique Factorization Monoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Examples.lean#L9-L10
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Examples.lean#L9-L10

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples
set_option autoImplicit false
open NagataFactoriality
open Polynomial

theorem NagataFactoriality.int_uniqueFactorizationMonoid : UniqueFactorizationMonoid ℤ := by sorry
