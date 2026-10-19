-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_coordinate_relations
-- name    : OAI.PiExponent.FormalInterpolation.bounded_representatives_of_coordinate_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:47:10.404601+00:00
-- url     : https://prove2.me/theorems/44fdca03-c569-4beb-91b5-8d4beeb60cb4
-- title:
--   Uniform monic coordinate relations give bounded monomial representatives
-- statement:
--   If every variable has a monic relation of the same positive degree modulo an ideal, every monomial has a congruent representative whose support exponents are all strictly less than that degree.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_representatives_of_coordinate_relations
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hN : 0 < N)
    (hrel : ∀ i : Fin (m + 1), ∃ c : Fin N → Complex,
      MvPolynomial.X i ^ N -
        ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J) :
    ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by sorry
