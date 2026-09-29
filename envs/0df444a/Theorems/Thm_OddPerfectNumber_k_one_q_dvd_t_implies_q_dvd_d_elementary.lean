-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q_dvd_t_implies_q_dvd_d_elementary
-- name    : OddPerfectNumber.k_one_q_dvd_t_implies_q_dvd_d_elementary
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:32:59.052373+00:00
-- url     : https://prove2.me/theorems/fa8f72fc-0972-416b-839a-a0b6b2ce623d
-- title:
--   Elementary transfer: q dividing the Euler cofactor t forces q dividing the Dris cofactor d
-- statement:
--   In the k = 1 unique-source configuration satisfying m^2 = ((p+1)/2)*d and sigma(m^2) = p*d with p prime and p = 1 mod 4, if a prime q divides the Euler cofactor (p+1)/2 and p divides sigma(q^a) for a the q-adic exponent of m^2, then q divides d. The intended proof is elementary and self-contained: writing Q = q^a, M for the q-coprime part of m^2 and T for the q-coprime part of (p+1)/2, the assumption that q does not divide d gives M = T*d and sigma(Q)*sigma(M) = p*d. Writing sigma(Q) = p*u with u > 0 yields d = u*sigma(M), hence M = T*u*sigma(M). Since sigma(M) >= M and T,u > 0 this forces sigma(M) = M and T*u = 1, so u = 1 and p = 1 + q + ... + q^a; therefore q divides p-1, while q dividing (p+1)/2 together with p = 1 mod 4 gives q dividing p+1, hence q divides 2, contradicting q odd. No Brent-Cohen-te Riele bound, no valuation-gap lemma, no unique-source hypothesis, and no quadratic-residue assumption is used. This theorem is published as an Open research child; no proof is asserted by this submission.
-- source:
--   Elementary reduction for the q-divides-t branch of the Odd Perfect Number mission (mission f37bda44-314b-4d8e-8917-fe26209e0c9c), intended to collapse that branch into the q-divides-d residual without the Brent-Cohen-te Riele Lemma 1 input used by OddPerfectNumber.k_one_q_dvd_d_of_q_dvd_t. Key ingredients are Mathlib's ordProj/ordCompl factorization API (Nat.ordProj_mul_ordCompl_eq_self, Nat.ordCompl_mul, Nat.coprime_ordCompl, Nat.ordCompl_eq_self_iff_zero_or_not_dvd), the divisor-sum bridge (ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow, Nat.Coprime.sum_divisors_mul), and Nat.sum_divisors_eq_sum_properDivisors_add_self for the collapse step.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q_dvd_t_implies_q_dvd_d_elementary (p m d q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime)
    (hqodd : Odd q)
    (hqdvd :
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (hqt : q ∣ (p + 1) / 2) :
    q ∣ d := by
  sorry

end OddPerfectNumber
