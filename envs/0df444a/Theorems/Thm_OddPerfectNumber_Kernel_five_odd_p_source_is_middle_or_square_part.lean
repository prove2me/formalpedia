-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_odd_p_source_is_middle_or_square_part
-- name    : OddPerfectNumber.Kernel.five_odd_p_source_is_middle_or_square_part
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T22:40:08.343112+00:00
-- url     : https://prove2.me/theorems/7d5867b0-de07-4445-8325-212b028d4402
-- title:
--   An incoming sigma source of the Euler prime is the middle block prime or divides the square part of m
-- statement:
--   If m equals 3 times u times a times b times d1 times q times r and a prime t divides m but is different from 3, q and r, then t divides the square part u a b d1. Combined with the proved quadratic nonresidue exclusions of 3 and of the minus block prime, this confines an incoming sigma source of the Euler prime to the middle block prime or to the square part of m.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- THE SOURCE LOCALISATION for the two-prime k = 5 branch.

Let `m = 3 * u * a * b * d1 * q * r` be the shape forced by the Proved
`five_two_prime_kernel_explicit_m` (223c7991), and let `t` be a prime dividing `m`.

Then `t = 3`, or `t = q`, or `t = r`, or `t` divides the square part `u * a * b * d1`.  This is
pure prime support splitting, by `Nat.Prime.dvd_mul` applied repeatedly.

COMBINED with the Proved exclusions this is the localisation the mission needs.  An incoming
sigma source of the Euler prime `p` satisfies

    p | 1 + t + ... + t ^ (2 e_t),   e_t = v_t(m),

so `t ^ (2 e_t + 1) = 1 (mod p)` with `2 e_t + 1` ODD, and therefore `orderOf (t : ZMod p)` is
ODD.  Now:

  * `t = 3` is impossible because `three_is_quadratic_nonresidue_mod_euler_prime` (f113d40e)
    says `(3/p) = -1` when `p % 3 = 2`, and a nonresidue has EVEN order
    (`odd_order_source_not_minus_block_prime`, 240feedb);
  * `t = r` is impossible because `r` divides `p ^ 2 - p + 1`, so
    `cyclotomic_minus_prime_square_iff_one_mod_twelve` (f0c98c1d) makes `r` a nonresidue when
    `r = 7 (mod 12)`, again EVEN order;
  * `t != p` automatically, since `t | m` and `p ∤ m`.

Hence the incoming Euler-prime source is the MIDDLE block prime `q`, or a prime dividing the
square part `u * a * b * d1`.  This statement is deliberately weaker than saying every prime of `m`
is excluded: it says where the source must LIVE, which is what the valuation budget needs. -/
theorem five_odd_p_source_is_middle_or_square_part (m u a b d1 q r t : Nat)
    (hshape : m = 3 * u * a * b * d1 * q * r)
    (ht : t.Prime)
    (htd : Dvd.dvd t m)
    (ht3 : t != 3) (htq : t != q) (htr : t != r) :
    t = q ∨ Dvd.dvd t (u * a * b * d1) ∨ t = r := by
  sorry

end OddPerfectNumber.Kernel
