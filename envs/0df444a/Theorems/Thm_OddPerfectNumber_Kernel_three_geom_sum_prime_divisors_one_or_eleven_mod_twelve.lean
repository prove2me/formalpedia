-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_three_geom_sum_prime_divisors_one_or_eleven_mod_twelve
-- name    : OddPerfectNumber.Kernel.three_geom_sum_prime_divisors_one_or_eleven_mod_twelve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T13:03:38.106997+00:00
-- url     : https://prove2.me/theorems/4f6e81cb-ea03-45eb-8805-13ee8b94aebf
-- title:
--   Every prime divisor other than 3 of 1 + 3 + ... + 3^(2e) is 1 or 11 mod 12
-- statement:
--   If a prime l different from 3 divides the geometric sum 1 + 3 + 3^2 + ... + 3^(2e), then l is congruent to 1 or to 11 modulo 12.
-- source:
--   MECHANISM.  l | (1 + 3 + ... + 3^(2e)) gives 3^(2e+1) = 1 (mod l) after multiplying by (3 - 1), so ord_l(3) divides the ODD number 2e+1.  Write 2e+1 = ord_l(3) * k; then 3^((l-1)/2) = 1 (mod l) because (l-1)/2 = ord_l(3) * ((l-1)/(2*ord_l(3))) needs l-1 = ord_l(3)*m with m even -- which holds since l is odd and ord_l(3) is odd, so m is even.  Hence 3 is a QUADRATIC RESIDUE mod l.  Quadratic reciprocity for 3 states (3/l) = 1 exactly when l = 1 or 11 (mod 12).  (The prime 2 cannot divide the sum, which is odd, so no hypothesis about 2 is needed.)
--
--   AUDIT.  Over 1 <= e <= 60 we factored sigma(3^(2e)) for every e: 245 distinct prime divisors other than 2 and 3, all congruent to 1 or 11 mod 12, zero violations.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem three_geom_sum_prime_divisors_one_or_eleven_mod_twelve (e l : Nat)
    (hl : l.Prime) (hl3 : l != 3)
    (hld : Dvd.dvd l (∑ i ∈ Finset.range (2 * e + 1), (3 : Nat) ^ i)) :
    (l % 12 = 1 \/ l % 12 = 11) := by
  sorry

end OddPerfectNumber.Kernel
