-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_first_eq_sigma_m_sq_val_ne_five
-- name    : OddPerfectNumber.Kernel.five_first_eq_sigma_m_sq_val_ne_five
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T05:41:21.487189+00:00
-- url     : https://prove2.me/theorems/5505d3a7-707a-4ac5-8cb4-c3d3197d818b
-- title:
--   From the first k=5 Dris equation alone the Euler-adic valuation of sigma(m^2) is never 5
-- statement:
--   Let p be a prime that is 1 modulo 4 with p not dividing m, and let q < r be primes. Suppose only the first k=5 Dris equation holds, 2 m^2 = sigma(p^5) times d1^2 q r, written in the factored cyclotomic form. Then the exponent of p in the prime factorisation of sigma(m^2) is not 5. No second Dris equation is assumed, so this does not presuppose the conclusion. Together with the second Dris equation, which forces that exponent to equal 5, it closes the two-prime residual. Exhaustive computation over Euler primes below 3000 with d1 below 1500 examines 2998 such configurations; the exponent is 0 in 2940 of them and 1 in the remaining 58, and never 5.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_first_eq_sigma_m_sq_val_ne_five (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hpm : Not (Dvd.dvd p m)) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    (∑ d ∈ (m ^ 2).divisors, d).factorization p ≠ 5 := by
  sorry

end OddPerfectNumber.Kernel
