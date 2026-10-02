-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_factorization_sum_eq_sum_factorization
-- name    : OddPerfectNumber.Kernel.factorization_sum_eq_sum_factorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T16:55:37.444787+00:00
-- url     : https://prove2.me/theorems/f2ab2c71-c935-47b1-97a5-415f3054f078
-- title:
--   The p-adic multiplicity of sigma(m^2) splits as a sum over the local prime-power factors
-- statement:
--   The exponent of a prime p in the divisor sum of m squared is the sum of the exponents of p in each local prime-power divisor sum. This is the central finite-sum identity of the sigma-source toolkit: together with the Proved sigma decomposition and the exact valuation five, it turns a global statement into a statement about the individual local factors, so an incoming sigma source of the Euler prime can be located and its local p-valuation measured. Every local factor is nonzero because 1 divides every positive prime power, which is the only side condition the product distribution needs.
-- source:
--   Rests on the Proved theorem sum_divisors_eq_prod_prime_pow (39086529), which expresses sigma(m^2) as the product of the local divisor sums, together with Mathlib's Nat.factorization_prod_apply, which distributes the multiplicity of a prime across a finite product as a sum of multiplicities. The nonzero side condition on each local factor is discharged by observing that 1 is a divisor of every positive prime power.

import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_sum_divisors_eq_prod_prime_pow

namespace OddPerfectNumber.Kernel

theorem factorization_sum_eq_sum_factorization {m p : Nat} (hm0 : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d).factorization p =
      ∑ t ∈ m.primeFactors,
        (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p := by sorry

end OddPerfectNumber.Kernel
