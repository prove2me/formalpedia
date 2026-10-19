-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_power_representative_step
-- name    : OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:40:00.824418+00:00
-- url     : https://prove2.me/theorems/254f5984-0f61-46b8-b3dd-5f7c9f271679
-- title:
--   Inductive step for bounded coordinate power representatives
-- statement:
--   Assuming every exponent strictly below n already has a representative supported only on coordinate i with exponent below N and congruent modulo J, construct such a representative for exponent n. For n < N, use the original monomial. Otherwise multiply the given degree-N relation by the needed power of X_i, then replace the lower powers using the induction hypothesis. The support and congruence bookkeeping for this step is the remaining core proof.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative_step
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hN : 0 < N)
    (i : Fin (m + 1))
    (n : Nat)
    (c : Fin N → Complex)
    (hpow : MvPolynomial.X i ^ N -
      ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J)
    (ih : ∀ r : Nat, r < n →
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
          MvPolynomial.monomial (Finsupp.single i r) (1 : Complex) - R ∈ J) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
        MvPolynomial.monomial (Finsupp.single i n) (1 : Complex) - R ∈ J := by sorry
