-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_dvd_two_mul_add_one_of_even_gives_three_mul_c_plus_one
-- name    : OddPerfectNumber.Kernel.five_dvd_two_mul_add_one_of_even_gives_three_mul_c_plus_one
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T14:14:41.609174+00:00
-- url     : https://prove2.me/theorems/0ba14d89-955d-4852-ba8b-8e80c3a2a708
-- title:
--   If a is even and 5 divides a + 2c + 1, then 5 divides 3c + a + 1
-- statement:
--   Let a be an even natural number and c a natural number.  If 5 divides a + 2c + 1, then 5 divides 3c + a + 1.
-- source:
--   MECHANISM.  2 is invertible modulo 5 with 2 * 3 = 6 = 1, so from 5 | a + 2c + 1 we get c = -3(a+1) (mod 5), equivalently 5 | 3c + a + 1.
--
--   CORRECTION, RECORDED BECAUSE IT MATTERS.  An earlier version of this child asserted `5 | c + a + 3`, which is FALSE: audited over even a < 400 and c < 400 it has 12800 violations, the first being a = 2, c = 1 (5 | 5 but 5 does not divide 6).  The evenness of `a` does NOT license replacing 3a by a -- the coefficient 3 comes from 2 * 3 = 1 (mod 5) and cannot be dropped.  The corrected conclusion 5 | 3c + a + 1 has 0 violations over the same 16000 cases.
--
--   WHY IT MATTERS FOR THE MISSION.  The first Dris equation fixes each exponent in m by 2 e_t = v_t(sigma(p^5)/2) + 2 v_t(d1) + [t = q] + [t = r], and the block exponents are even, so 2 e_t + 1 = a + 2c + 1 with a EVEN and c = v_t(d1).  The corrected incoming-source criterion for the Euler prime 5 requires 5 | 2 e_t + 1, and this lemma turns that into a congruence on v_t(d1) -- the first statement in this branch linking the Euler prime to d1. With a = 2 it gives 5 | 3 v_t(d1) + 3, i.e. v_t(d1) = 1 (mod 5).

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_dvd_two_mul_add_one_of_even_gives_three_mul_c_plus_one (a c : Nat)
    (ha : Even a) (h5 : Dvd.dvd 5 (a + 2 * c + 1)) :
    Dvd.dvd 5 (3 * c + a + 1) := by
  sorry

end OddPerfectNumber.Kernel
