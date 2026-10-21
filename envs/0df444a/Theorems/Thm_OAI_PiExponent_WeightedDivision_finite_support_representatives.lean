-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_finite_support_representatives
-- name    : OAI.PiExponent.WeightedDivision.finite_support_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:27:21.466623+00:00
-- url     : https://prove2.me/theorems/054b6a52-7556-48cd-a9bd-30f54a30cf97
-- title:
--   Finite-support lifting of monomial representatives
-- statement:
--   If every exponent in a polynomial's finite support has a monomial representative modulo the ideal supported on exponents satisfying A, then the polynomial has a representative modulo the ideal supported on exponents satisfying A.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.finite_support_representatives
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (F : MvPolynomial ι R)
    (hF : ∀ v ∈ F.support,
      ∃ Q : MvPolynomial ι R,
        MvPolynomial.monomial v (1 : R) - Q ∈ J ∧
          ∀ w ∈ Q.support, A w) :
    ∃ Q : MvPolynomial ι R,
      F - Q ∈ J ∧ ∀ w ∈ Q.support, A w := by sorry
