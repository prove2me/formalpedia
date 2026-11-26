-- Prove2me | Theorems.Thm_NagataFactoriality_polynomial_uniqueFactorizationMonoid_of_laurent
-- name    : NagataFactoriality.polynomial_uniqueFactorizationMonoid_of_laurent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:35.807143+00:00
-- url     : https://prove2.me/theorems/444f4621-ac36-4b82-8da8-6a56f2e78613
-- title:
--   Nagata Factoriality: polynomial unique Factorization Monoid of laurent
-- statement:
--   The Nagata Factoriality construction uses the polynomial unique Factorization Monoid of laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L87-L95
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L87-L95

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

theorem NagataFactoriality.polynomial_uniqueFactorizationMonoid_of_laurent {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R[T;T⁻¹]] :
    UniqueFactorizationMonoid R[X] := by sorry
