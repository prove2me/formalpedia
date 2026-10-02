-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_dvd_three_term_sum_mod_p_gives_one_mod_three
-- name    : OddPerfectNumber.Kernel.dvd_three_term_sum_mod_p_gives_one_mod_three
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T21:48:43.838659+00:00
-- url     : https://prove2.me/theorems/6618ee35-d712-458e-83a2-47cf2f93be29
-- title:
--   A prime dividing a three-term sum of one is congruent to one modulo three
-- statement:
--   Let p be a prime at least five, and let t be a natural number. Suppose p divides 1 + t + t squared and t is not congruent to 1 modulo p. Then p is congruent to 1 modulo 3. Indeed multiplying the divisibility by t minus 1 shows that t cubed is congruent to 1 modulo p, so the multiplicative order of t modulo p divides 3; it is not 1 because t is not congruent to 1 modulo p, so the order is 3; and an element of order 3 can exist modulo p only when 3 divides p minus 1, that is when p is congruent to 1 modulo 3. This is what makes the Euler prime unable to be supplied by a cyclotomic prime of exponent one in the branch where neither kernel prime is 3, since in that branch p is congruent to 2 modulo 3.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem dvd_three_term_sum_mod_p_gives_one_mod_three {p t : Nat} (hp : p.Prime)
    (hp5 : 5 ≤ p) (ht1 : t % p ≠ 1)
    (h : Dvd.dvd p (1 + t + t ^ 2)) :
    p % 3 = 1 := by
  sorry

end OddPerfectNumber.Kernel
