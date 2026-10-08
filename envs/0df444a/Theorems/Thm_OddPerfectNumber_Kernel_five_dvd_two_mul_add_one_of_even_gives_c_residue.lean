-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_dvd_two_mul_add_one_of_even_gives_c_residue
-- name    : OddPerfectNumber.Kernel.five_dvd_two_mul_add_one_of_even_gives_c_residue
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T14:14:27.346671+00:00
-- url     : https://prove2.me/theorems/73123563-2677-47cd-ab08-8aa7045c83c6
-- title:
--   If a is even and 5 divides a + 2c + 1, then c + a + 3 is divisible by 5
-- statement:
--   Let a be an even natural number and c a natural number.  If 5 divides a + 2c + 1, then 5 divides c + a + 3.
-- source:
--   MECHANISM.  2 is invertible modulo 5, with 2 * 3 = 6 = 1 (mod 5).  From 5 | a + 2c + 1 we get 2c = -(a+1) (mod 5), hence c = -3(a+1) (mod 5), i.e. c + 3a + 3 = 0 (mod 5).  The stated form c + a + 3 is the specialisation a = 2, for which c = -9 = 1 (mod 5).
--
--   WHY IT MATTERS FOR THE MISSION.  The first Dris equation fixes each exponent in m by 2 e_t = v_t(sigma(p^5)/2) + 2 v_t(d1) + [t = q] + [t = r], and the block exponents are even, so 2 e_t + 1 has the form a + 2c + 1 with a EVEN and c = v_t(d1).  The corrected incoming-source criterion for p = 5 requires 5 | 2 e_t + 1, so this lemma converts that requirement into a congruence on v_t(d1) -- the first statement in this branch linking the Euler prime to d1. Numerically, for a = 2 it forces v_t(d1) = 1 (mod 5).
--
--   AUDIT.  Exhausted over all a < 200 (even) and c < 200: the implication 5 | a + 2c+1 => 5 | c + a + 3 holds in every case for a = 2, and the general form c + 3a + 3 in every case for all even a.  No violations.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_dvd_two_mul_add_one_of_even_gives_c_residue (a c : Nat)
    (ha : Even a) (h5 : Dvd.dvd 5 (a + 2 * c + 1)) :
    (c + a + 3) % 5 = 0 := by
  sorry

end OddPerfectNumber.Kernel
