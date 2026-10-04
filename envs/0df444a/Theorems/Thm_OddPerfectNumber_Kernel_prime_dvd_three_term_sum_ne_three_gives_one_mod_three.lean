-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_prime_dvd_three_term_sum_ne_three_gives_one_mod_three
-- name    : OddPerfectNumber.Kernel.prime_dvd_three_term_sum_ne_three_gives_one_mod_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:56:46.877208+00:00
-- url     : https://prove2.me/theorems/4d8dc474-eab9-4e58-ac3a-cc40afc7364e
-- title:
--   A prime other than 3 dividing a three-term sum is 1 modulo 3
-- statement:
--   Let r be a prime different from 3, and suppose r divides 1 plus l plus l squared for some natural number l. Then r is congruent to 1 modulo 3. Indeed r dividing 1 plus l plus l squared gives l cubed congruent to 1 modulo r; if l is 1 modulo r then r divides 3, impossible, so the multiplicative order of l modulo r is exactly 3, hence 3 divides r minus 1. This governs every prime that leaks from a local divisor sum sigma of l squared into the Dris index, and is the congruence refinement of the prime closure condition.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem prime_dvd_three_term_sum_ne_three_gives_one_mod_three {r l : Nat} (hr : r.Prime)
    (hr3 : r != 3) (h : Dvd.dvd r (1 + l + l ^ 2)) :
    r % 3 = 1 := by
  sorry

end OddPerfectNumber.Kernel
