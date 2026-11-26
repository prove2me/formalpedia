-- Prove2me | Theorems.Thm_NagataFactoriality_iterated_polynomial_uniqueFactorizationMonoid_via_nagata
-- name    : NagataFactoriality.iterated_polynomial_uniqueFactorizationMonoid_via_nagata
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:15.265111+00:00
-- url     : https://prove2.me/theorems/7840ffa8-86cc-4ac3-a970-f489f8b33bc1
-- title:
--   Nagata Factoriality: iterated polynomial unique Factorization Monoid via nagata
-- statement:
--   The Nagata Factoriality construction uses the iterated polynomial unique Factorization Monoid via nagata property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L102-L107
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L102-L107

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Definitions.Def_NagataFactoriality_Applications_Laurent
set_option autoImplicit false
open NagataFactoriality
open scoped LaurentPolynomial
open Polynomial

theorem NagataFactoriality.iterated_polynomial_uniqueFactorizationMonoid_via_nagata
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid (Polynomial (Polynomial R)) := by sorry
