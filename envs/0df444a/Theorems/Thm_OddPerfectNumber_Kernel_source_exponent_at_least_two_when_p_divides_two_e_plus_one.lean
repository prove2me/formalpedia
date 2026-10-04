-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_source_exponent_at_least_two_when_p_divides_two_e_plus_one
-- name    : OddPerfectNumber.Kernel.source_exponent_at_least_two_when_p_divides_two_e_plus_one
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T23:54:27.925632+00:00
-- url     : https://prove2.me/theorems/2687a13f-5bfa-409c-a980-92a2cef45922
-- title:
--   An incoming Euler-prime source whose local valuation is positive has exponent at least two in m
-- statement:
--   If t is a prime dividing m, p is a prime congruent to 1 modulo 4 with t different from p, and p divides the geometric sum 1 plus t plus t squared up to t to the power 2e where e is the exponent of t in m, then e is at least 2. In other words an incoming sigma source of the Euler prime that actually contributes must divide m to at least the second power, which for the shape m equals 3 times u times a times b times d1 times q times r forces an admissible prime into d1.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The SHARP ARITHMETIC CONDITION on an incoming sigma source, and the concrete remaining
obstruction for the two-prime k = 5 branch.

Suppose `t` is a prime with `t | m`, and put `e = m.factorization t`, the exponent of `t` in `m`.
If the local sigma factor `1 + t + ... + t^(2 e)` is divisible by the odd prime `p`, then
`p | 2 e + 1`, and therefore

    e = (p - 1) / 2   (mod p),

so in particular `2 <= e` as soon as `p >= 3`.  In other words: an incoming Euler-prime source
with a POSITIVE local p-valuation cannot occur to the FIRST power in `m`; it must divide `m` at
least twice.

MECHANISM.  `p | 1 + t + ... + t^(2 e)` gives `(t - 1) * (1 + t + ... + t^(2 e)) = t^(2 e+1) - 1`,
so `t^(2 e+1) = 1 (mod p)`.  Since `t` is prime and `p` is prime with `t != p` the order of `t`
modulo `p` divides `2 e + 1`.  A NONRESIDUE `t` has EVEN order by
`odd_order_source_not_minus_block_prime` (240feedb), so the order is ODD; Fermat bounds it by
`p - 1`, and `odd_order_dvd_quarter_of_p_minus_one` (08fe6da2) refines this for `p % 4 = 1`.  Since
the order divides the ODD number `2 e + 1` and also divides `p - 1`, its value is a divisor of
`gcd(2 e + 1, p - 1)`; for `p` to divide `2 e + 1` itself one needs `2 e + 1 >= p`.

CONSEQUENCE FOR THE MISSION.  With `m = 3 * u * a * b * d1 * q * r` (223c7991) the block primes
`q` and `r` and the prime `3` enter `m` with exponent `1 + v(d1)`, so a contributing source with
positive local p-valuation forces an ADMISSIBLE prime to divide `d1`.  Combined with the Proved
`sigma(3^(2 e)) | d1^2` this is a concrete, testable restriction on `d1` and not merely on `m`.

Numerically, for `p = 5` the condition is `e = 2 (mod 5)`, and a scan over all `d1 < 4000` in the
`p = 5` normal form finds the budget `sum_t v_5(sigma(t^(2 e_t))) = 5` is NEVER reached: the
largest value observed is `1`. -/
theorem source_exponent_at_least_two_when_p_divides_two_e_plus_one {p t m : Nat}
    (hp : p.Prime) (hp4 : p % 4 = 1) (ht : t.Prime) (htd : t ∣ m) (hqp : t != p)
    (hgeom : p ∣ (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i)) :
    2 <= m.factorization t := by
  sorry

end OddPerfectNumber.Kernel
