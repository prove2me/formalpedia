-- Prove2me | Theorems.Thm_NagataFactoriality_laurentPolynomial_isLocalization
-- name    : NagataFactoriality.laurentPolynomial_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:00.679513+00:00
-- url     : https://prove2.me/theorems/de93efca-7c67-41dd-abf0-e2747fac6732
-- title:
--   Nagata Factoriality: laurent Polynomial is Localization
-- statement:
--   The Nagata Factoriality construction uses the laurent Polynomial is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L13-L15
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Applications/Laurent.lean#L13-L15

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

theorem NagataFactoriality.laurentPolynomial_isLocalization (R : Type*) [CommSemiring R] :
    IsLocalization.Away (X : R[X]) R[T;T⁻¹] := by sorry
