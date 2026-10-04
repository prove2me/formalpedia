-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_sigma_m_sq_val_ne_five
-- name    : OddPerfectNumber.Kernel.five_two_prime_sigma_m_sq_val_ne_five
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T05:14:54.543872+00:00
-- url     : https://prove2.me/theorems/5bf1634b-3600-4aa5-94d4-7f63e0c4db1e
-- title:
--   In the k=5 two-prime branch the Euler-adic valuation of sigma(m^2) is never 5
-- statement:
--   Let p be a prime that is 1 modulo 4 and let q < r be primes. Suppose both k=5 Dris equations hold with square-free index s = d1^2 * q * r, that is 2 m^2 = sigma(p^5) s and sigma(m^2) = p^5 s. Then the exponent of p in the prime factorisation of sigma(m^2) is not 5. Since the second Dris equation writes sigma(m^2) as p^5 times an index that is not divisible by p, that exponent is forced to be exactly 5, so this child contradicts the hypotheses and closes the two-prime residual. Exhaustive computation over Euler primes p below 20000 with d1 below 2000 finds the exponent always 0, or, only for p = 5, exactly 1; it is never 5, and across all kernel sizes it never exceeds 4.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_sigma_m_sq_val_ne_five (p m d1 q r : Nat) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    (∑ d ∈ (m ^ 2).divisors, d).factorization p ≠ 5 := by
  sorry

end OddPerfectNumber.Kernel
