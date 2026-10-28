-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_prime_height_add_trdeg
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_trdeg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:59:16.195867+00:00
-- url     : https://prove2.me/theorems/d7a109fe-c296-409a-ac0f-9b6b51f581a2
-- title:
--   Height and transcendence degree bound for polynomial primes
-- statement:
--   For a prime ideal in a polynomial ring over the complex numbers with `m + 1` variables, its height plus the transcendence degree of the fraction field of the quotient is at least the number of variables. The boundary cases include the zero prime, where the transcendence degree is `m + 1`, and maximal ideals, where the height is `m + 1`.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_trdeg
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height +
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by
  sorry
