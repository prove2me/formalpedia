-- Prove2me | Theorems.Thm_NagataFactoriality_polynomial_uniqueFactorizationMonoid_via_nagata
-- name    : NagataFactoriality.polynomial_uniqueFactorizationMonoid_via_nagata
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:25.22694+00:00
-- url     : https://prove2.me/theorems/3f9723b8-64c5-432c-a40d-d4f53d27eed3
-- title:
--   Nagata Factoriality: polynomial unique Factorization Monoid via nagata
-- statement:
--   The Nagata Factoriality construction uses the polynomial unique Factorization Monoid via nagata property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L97-L100
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L97-L100

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

theorem NagataFactoriality.polynomial_uniqueFactorizationMonoid_via_nagata {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[X] := by sorry
