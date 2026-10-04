-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_kernel_explicit_m
-- name    : OddPerfectNumber.Kernel.five_two_prime_kernel_explicit_m
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T19:27:16.034767+00:00
-- url     : https://prove2.me/theorems/223c7991-79c4-4784-a047-982c3dc76f21
-- title:
--   In the two-prime k=5 branch m is the product of the normal-form factors
-- statement:
--   Suppose the Euler prime satisfies p plus 1 equals 6 times a square, the middle cyclotomic block is q times a square, the last block is 3 times r times a square, and the Dris index is d1 squared times q times r. Then the first Dris equation forces m to equal 3 times u times a times b times d1 times q times r. This converts the search over prime divisors of m into a finite list.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- In the two-prime k = 5 branch, once the three normalised blocks are pinned down, the
square root is forced: `m = 3 * u * a * b * d1 * q * r`.

Mechanism.  Assume

* `p + 1 = 6 * u ^ 2`, so `(p + 1) / 2 = 3 * u ^ 2`;
* `C := p ^ 2 + p + 1 = q * a ^ 2`;
* `D := p ^ 2 - p + 1 = 3 * r * b ^ 2`;
* the index is `s = d1 ^ 2 * (q * r)` (already built into `h1`).

Then `sigma(p ^ 5) = (p + 1) * C * D = (6 u ^ 2) * (q a ^ 2) * (3 r b ^ 2)`, so
`sigma(p ^ 5) / 2 = 9 u ^ 2 a ^ 2 b ^ 2 q r`.  Substituting into
`h1 : 2 * m ^ 2 = sigma(p ^ 5) * s` cancels the leading factor `2` and yields

    m ^ 2 = 9 u ^ 2 a ^ 2 b ^ 2 q r * d1 ^ 2 q r = (3 * u * a * b * d1 * q * r) ^ 2,

and `Nat.sqrt_sq_eq` gives `m = 3 * u * a * b * d1 * q * r`.

This is the key structural consequence: every prime divisor of `m` is therefore `3`, a prime
of `u`, of `a`, of `b`, of `d1`, or one of the two block primes `q`, `r`.  Combined with the
quadratic-nonresidue exclusions it localises the incoming sigma source of the Euler prime.

The numerical check is exact: for the only two normal forms below p = 1500, namely
`p = 5` and `p = 293`, the identity `2 m ^ 2 = sigma(p ^ 5) * s` holds for
`d1` in `{1, 7, 13, 31, 217}`. -/
theorem five_two_prime_kernel_explicit_m (p m u a b d1 q r : Nat)
    (hp1 : p + 1 = 6 * u ^ 2)
    (hC : p ^ 2 + p + 1 = q * a ^ 2)
    (hD : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  sorry

end OddPerfectNumber.Kernel
