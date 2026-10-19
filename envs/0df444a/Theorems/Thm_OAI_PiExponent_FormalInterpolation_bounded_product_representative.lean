-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_product_representative
-- name    : OAI.PiExponent.FormalInterpolation.bounded_product_representative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:36:30.876918+00:00
-- url     : https://prove2.me/theorems/db5684a1-2d9b-4a17-b6c6-07363374ad35
-- title:
--   Multiply bounded coordinate representatives
-- statement:
--   If each coordinate power in a monomial has a congruent representative supported only on that coordinate and bounded there by `N`, multiplying those representatives gives a congruent representative whose every support exponent is below `N`.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_product_representative
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (a : Fin (m + 1) →₀ Nat)
    (hcoord : ∀ i : Fin (m + 1),
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
          MvPolynomial.monomial (Finsupp.single i (a i)) (1 : Complex) - R ∈ J) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
        MvPolynomial.monomial a (1 : Complex) - R ∈ J := by sorry
