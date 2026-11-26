-- Prove2me | Theorems.Thm_NagataFactoriality_polynomial_prime_X
-- name    : NagataFactoriality.polynomial_prime_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:05.118115+00:00
-- url     : https://prove2.me/theorems/42137d63-e7b8-4d7e-b959-ea86a760a510
-- title:
--   Nagata Factoriality: polynomial prime X
-- statement:
--   The Nagata Factoriality construction uses the polynomial prime X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L17-L19
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L17-L19

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

theorem NagataFactoriality.polynomial_prime_X {R : Type*} [CommRing R] [IsDomain R] :
    Prime (Polynomial.X : R[X]) := by sorry
