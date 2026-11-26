-- Prove2me | Theorems.Thm_NagataFactoriality_polynomial_toLaurent_prime_of_not_dvd_X
-- name    : NagataFactoriality.polynomial_toLaurent_prime_of_not_dvd_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:12.802814+00:00
-- url     : https://prove2.me/theorems/8f385ee9-2820-5239-b646-76adfef5df0c
-- title:
--   Nagata Factoriality: polynomial to Laurent prime of not dvd X
-- statement:
--   The Nagata Factoriality construction uses the polynomial to Laurent prime of not dvd X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L21-L40
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L21-L40

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

theorem NagataFactoriality.polynomial_toLaurent_prime_of_not_dvd_X {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : Prime p) (hX : ¬ p ∣ X) : Prime (Polynomial.toLaurent p) := by sorry
