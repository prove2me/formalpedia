-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_power_representative
-- name    : OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:36:14.698907+00:00
-- url     : https://prove2.me/theorems/9d926c70-8d86-4fb7-b9c4-bde96900ee79
-- title:
--   Reduce one coordinate power using a monic relation
-- statement:
--   Given a degree-`N` monic relation for one variable modulo `J`, every power of that variable has a congruent representative supported only on that variable and with exponent strictly below `N`.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hN : 0 < N)
    (i : Fin (m + 1))
    (n : Nat)
    (c : Fin N → Complex)
    (hpow : MvPolynomial.X i ^ N -
      ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
        MvPolynomial.monomial (Finsupp.single i n) (1 : Complex) - R ∈ J := by sorry
