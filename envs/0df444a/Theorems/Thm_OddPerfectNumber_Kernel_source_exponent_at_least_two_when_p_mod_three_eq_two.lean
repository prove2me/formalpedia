-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_source_exponent_at_least_two_when_p_mod_three_eq_two
-- name    : OddPerfectNumber.Kernel.source_exponent_at_least_two_when_p_mod_three_eq_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:57:02.411072+00:00
-- url     : https://prove2.me/theorems/eb54aaab-c458-48e7-bd52-4999267a4553
-- title:
--   An incoming Euler-prime source with positive local valuation must occur to at least the second power in m when p is 2 modulo 3
-- statement:
--   Let t be a prime dividing m and let e be the exponent of t in m. Let p be a prime that is 2 modulo 3, different from t. If p divides the geometric sum 1 + t + t squared + ... + t to the power 2e, then e is at least 2. So for an Euler prime congruent to 2 modulo 3, a sigma source that genuinely contributes to the p-adic valuation must divide m at least twice.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The SHARP ARITHMETIC CONDITION on an incoming sigma source for the k = 5 branch.

Suppose `t` is a prime with `t | m`, and put `e = m.factorization t`, the exponent of `t` in `m`.
If the local sigma factor `1 + t + ... + t^(2 e)` is divisible by the prime `p = 2 (mod 3)`,
then `e >= 2`.

In other words: for an Euler prime that is `2 (mod 3)`, an incoming sigma source which actually
contributes to `v_p` cannot occur to the FIRST power in `m`.

MECHANISM.  `e = 0` gives `1 + t + t^0 = 1`, and `p | 1` is impossible for `p >= 2`.  So
suppose `e = 1`.  Then `p | 1 + t + t^2`, so `t^3 = 1 (mod p)`.  Either `t = 1 (mod p)`, in
which case `1 + t + t^2 = 3 (mod p)` forces `p = 3`, contradicting `p % 3 = 2`; or else
`ord_p t = 3`, so `3 | p - 1`, again contradicting `p % 3 = 2`.  Both exits fail.

WHY `p % 3 = 2` AND NOT THE STRONGER `p % 4 = 1`.  The sibling statement
`source_exponent_at_least_two_when_p_divides_two_e_plus_one`, which assumed only
`p % 4 = 1`, is FALSE: `p = 13, t = 3, e = 1` gives `1 + 3 + 9 = 13`.  Every counterexample
of that shape has `p = 1 (mod 3)`, because the exit `3 | p - 1` is precisely the
counterexample mechanism.  The mission's first-equation congruences force `p = 5 (mod 48)`,
hence `p = 2 (mod 3)`, so this corrected hypothesis is available where it is needed and the
counterexample family is excluded.

CONSEQUENCE FOR THE MISSION.  With `m = 3 * u * a * b * d1 * q * r` the primes `3`, `q` and `r`
enter `m` with exponent `1 + v(d1)`, and every prime dividing `u`, `a` or `b` enters with
exponent `2 + v(d1)` or more.  A contributing source with positive local `p`-valuation therefore
cannot be one of those block primes at exponent one; an ADMISSIBLE prime must reach `d1`.
Combined with the Proved `sigma(3^(2 e)) | d1^2` this is a concrete restriction on `d1`. -/
theorem source_exponent_at_least_two_when_p_mod_three_eq_two {p t m : Nat}
    (hp : p.Prime) (hp3 : p % 3 = 2) (ht : t.Prime) (htd : t ∣ m) (hqp : t != p)
    (hgeom : p ∣ (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i)) :
    2 <= m.factorization t := by
  sorry

end OddPerfectNumber.Kernel
