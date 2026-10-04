-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_dris_odd_multiplicity_p_source
-- name    : OddPerfectNumber.Kernel.five_dris_odd_multiplicity_p_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T11:02:38.591302+00:00
-- url     : https://prove2.me/theorems/b860b1b5-8412-4146-ae03-18a690430e81
-- title:
--   The two-prime k=5 residual supplies a local sigma source of the Euler prime of odd multiplicity
-- statement:
--   Assume the two-prime square-free-index k=5 Dris residual: the Euler prime p is an odd prime congruent to 1 modulo 4 that does not divide m, the index is d1 squared times two distinct primes q and r, and both Dris equations hold. Then some prime t dividing m has its own local geometric sum divisible by the Euler prime p, and p occurs in that local factor to an odd multiplicity. The oddness is forced because the second Dris equation together with p not dividing the index makes the total p-adic valuation of the divisor sum exactly five, which is odd.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- In the two-prime square-free-index k=5 residual there is a prime `t` dividing `m`
such that

  * `p` divides the local geometric sum `sum i in range (2 * m.factorization t + 1), t ^ i`, and
  * `p` occurs in that local factor to an ODD multiplicity.

The two ingredients are the Proved `five_dris_one_index_not_dvd_euler` (a4779371), which
gives `Not (p | d1^2 * (q * r))`, and the Proved
`factorization_p_of_mul_prime_pow_ne` (925fa028), which turns that together with the second
Dris equation into `(sigma(m^2)).factorization p = 5`.  The extraction is the Proved
`index_prime_odd_multiplicity_source_not_euler_dvd` (9a610274), applied with the residual's
own `Not (p | m)`.

This is the first child that speaks about the SECOND Dris equation inside the two-prime
residual. -/
theorem five_dris_odd_multiplicity_p_source (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : Not (Dvd.dvd p m))
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\
      Dvd.dvd p (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p)) := by
  sorry

end OddPerfectNumber.Kernel
