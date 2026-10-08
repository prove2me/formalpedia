-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_p_valuation_sum_eq_five
-- name    : OddPerfectNumber.Kernel.five_p_valuation_sum_eq_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:59:15.276554+00:00
-- url     : https://prove2.me/theorems/62ad4aeb-df4a-4690-a12f-c134e3dc2a17
-- title:
--   Local p-valuations of the sigma factors sum to exactly five
-- statement:
--   Under the second Dris equation sigma(m^2) = p^5*s with p prime not dividing s, the p-adic valuations of the local sigma factors sum to exactly 5. The sigma-product theorem writes sigma(m^2) as the product over t in m.primeFactors of sigma(t^(2*v_t(m))); taking Nat.factorization at p turns the product into the finite sum (every local divisor sum is positive, hence nonzero), and the right-hand side has p-factorization exactly 5 by the prime-power factorization helper. Since 5 is odd, some local factor carries an odd p-valuation: the entry point to the incoming p-source analysis for the k=5 two-prime residual.
-- source:
--   Valuation-budget bridge for 6eb10265: composes Proved sum_divisors_eq_prod_prime_pow with Proved factorization_p_of_mul_prime_pow_ne. p not dividing s excludes s = 0 (p divides 0), so no separate s != 0 hypothesis is needed.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_p_valuation_sum_eq_five (p m s : Nat)
    (hp : p.Prime)
    (hm0 : m != 0)
    (hps : Not (Dvd.dvd p s))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    ∑ t ∈ m.primeFactors,
      ((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p) = 5 := by
  sorry

end OddPerfectNumber.Kernel
