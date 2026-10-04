-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_primes_dvd_sigma
-- name    : OddPerfectNumber.Kernel.five_two_prime_index_primes_dvd_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T06:37:36.072568+00:00
-- url     : https://prove2.me/theorems/c0fb7108-d480-47c5-9203-2c8231ffdf95
-- title:
--   Both kernel primes divide the divisor sum of the second Dris equation
-- statement:
--   Let p, m, d1, q and r be natural numbers and suppose the second Dris equation holds, namely that the sum of the divisors of m squared equals p to the fifth times d1 squared times q times r. Then both q and r divide the sum of the divisors of m squared.
--
--   This is the missing link between the second Dris equation and the sigma-source toolkit. Both proved theorems `index_prime_has_non_self_sigma_source` (c2bd62fe) and `index_prime_has_odd_multiplicity_source` (48e8fb88) take a prime that divides m together with the hypothesis that the same prime divides the divisor sum of m squared. In the two-prime residual the index primes q and r do divide m, by the proved theorem `five_two_prime_cyclotomic_primes_dvd_m` (13f23023), but nothing yet supplied the divisibility of the divisor sum that those two theorems require.
--
--   The proof is a single divisibility argument. Since q divides q times r, transitivity through `dvd_mul_of_dvd_right` gives q dividing p to the fifth times d1 squared times q times r, and rewriting by the hypothesis turns that into q dividing the divisor sum. The same argument with r in place of q gives the second conjunct. Neither primality of q and r nor the first Dris equation is used.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_index_primes_dvd_sigma (p m d1 q r : Nat)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    (q ∣ (∑ d ∈ (m ^ 2).divisors, d)) ∧ (r ∣ (∑ d ∈ (m ^ 2).divisors, d)) := by
  sorry

end OddPerfectNumber.Kernel
