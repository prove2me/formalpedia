-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_local_sigma_odd_prime_pow_dvd
-- name    : OddPerfectNumber.Kernel.local_sigma_odd_prime_pow_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:56:17.230296+00:00
-- url     : https://prove2.me/theorems/61e29280-b6cb-4e5b-862f-0d9688fa4950
-- title:
--   A local divisor sum at an even exponent divides the divisor sum of a square
-- statement:
--   Let m be a natural number, t a prime dividing m squared, and e the exponent of t in m squared, so that e equals twice the exponent of t in m. Then the local divisor sum of t to the power e divides the divisor sum of m squared. Equivalently every prime power appearing in m supplies a local factor of sigma of m squared that divides it.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem local_sigma_odd_prime_pow_dvd {m t : Nat} (ht : t.Prime) (htd : Dvd.dvd t (m ^ 2))
    (he : 1 ≤ (m ^ 2).factorization t) :
    Dvd.dvd (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) (∑ d ∈ (m ^ 2).divisors, d) := by
  sorry

end OddPerfectNumber.Kernel
