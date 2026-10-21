-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_polynomial_representatives_of_monomial_representatives
-- name    : OAI.PiExponent.WeightedDivision.polynomial_representatives_of_monomial_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:55:19.886545+00:00
-- url     : https://prove2.me/theorems/ad7445bc-0ef5-470b-b964-3ec67b7d7300
-- title:
--   Assemble allowed representatives over a finite polynomial expansion
-- statement:
--   If every coefficient monomial has an allowed-supported representative modulo J, then every polynomial does, by combining representatives across its finite monomial expansion.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.polynomial_representatives_of_monomial_representatives
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (hmono : ∀ (u : ι →₀ ℕ) (c : R),
      ∃ Q : MvPolynomial ι R,
        MvPolynomial.monomial u c - Q ∈ J ∧ ∀ v ∈ Q.support, A v)
    (P : MvPolynomial ι R) :
    ∃ Q : MvPolynomial ι R,
      P - Q ∈ J ∧ ∀ u ∈ Q.support, A u := by sorry
