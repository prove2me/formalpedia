-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_quarter_not_dvd_three_of_five_mod_forty_eight
-- name    : OddPerfectNumber.Kernel.quarter_not_dvd_three_of_five_mod_forty_eight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T05:17:59.764286+00:00
-- url     : https://prove2.me/theorems/2244ac7a-c0ca-4e89-8064-2e079f6b638d
-- title:
--   For p congruent to 5 modulo 48 the quarter of p minus one is not divisible by 3
-- statement:
--   Let p be a natural number with p congruent to 5 modulo 48. Then (p - 1) / 4 is congruent to 1 modulo 3, and in particular 3 does not divide (p - 1) / 4. Indeed p - 1 is congruent to 4 modulo 48, so writing p - 1 = 48k + 4 gives (p - 1)/4 = 12k + 1, which is 1 modulo 3. This is the congruence that splits the incoming sigma source of the Euler prime into two regimes: either the multiplicative order of the source modulo p is 1, or it is an odd number at least 5, since order 3 would require 3 to divide (p-1)/4.
-- source:
--   Elementary modular arithmetic. From p % 48 = 5 one has p - 1 = 48k + 4 for some k, so 4 divides p - 1 exactly and (p-1)/4 = 12k + 1. Reducing 12k + 1 modulo 3 gives 1, so 3 does not divide it. No number theory beyond the division algorithm is involved.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem quarter_not_dvd_three_of_five_mod_forty_eight (p : Nat)
    (h48 : p % 48 = 5) :
    Not (Dvd.dvd 3 ((p - 1) / 4)) := by
  sorry

end OddPerfectNumber.Kernel
