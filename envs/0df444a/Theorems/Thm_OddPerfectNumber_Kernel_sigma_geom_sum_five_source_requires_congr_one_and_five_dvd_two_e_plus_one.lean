-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_geom_sum_five_source_requires_congr_one_and_five_dvd_two_e_plus_one
-- name    : OddPerfectNumber.Kernel.sigma_geom_sum_five_source_requires_congr_one_and_five_dvd_two_e_plus_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T14:00:57.489589+00:00
-- url     : https://prove2.me/theorems/66c4323c-2905-4057-b634-d936e5a058a3
-- title:
--   A prime p = 5 dividing 1+t+...+t^(2e) forces t = 1 mod 5 or 5 to divide 2e+1
-- statement:
--   Let t be a prime different from 5.  If 5 divides the geometric sum 1 + t + ... + t^(2e), then either t is congruent to 1 modulo 5, or 5 divides 2e+1.
-- source:
--   MECHANISM.  The Proved theorem OddPerfectNumber.geom_sum_dvd_implies_order_dvd gives ord_5(t) | 2e+1, and 2e+1 is ODD, so ord_5(t) is ODD.  If t is not congruent to 1 modulo 5 then ord_5(t) > 1, hence it is an odd prime divisor of 5 - 1 = 4, which is impossible since 4 has no odd divisor greater than 1.  Therefore t = 1 (mod 5).  The disjunct 5 | 2e+1 is included because it is the necessary condition in the t = 1 case as well: then sigma(t^(2e)) = 2e+1 (mod 5) by LTE, so 5 | sigma forces 5 | 2e+1.
--
--   WHY IT MATTERS.  This corrects an earlier, WRONG claim that the incoming source for the Euler prime 5 must be t = 3.  ord_5(3) = 4 is EVEN, so 3 divides no sigma(3^(2e)) at all: directly, sigma(3^4) = 121 = 11^2 and 5 does not divide 121.  The earlier argument used only the necessary condition 5 | 2e+1 and wrongly treated it as sufficient.
--
--   AUDIT.  For primes t < 300 with EVEN ord_5(t) and 1 <= e < 40: 1794 cases, 0 with 5 | sigma(t^(2e)).  For primes t = 1 (mod 5): 120 cases with 5 | sigma(t^(2e)), 0 of which violate 5 | 2e+1.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_geom_sum_five_source_requires_congr_one_and_five_dvd_two_e_plus_one (t e : Nat)
    (ht : t.Prime) (ht5 : Not (Dvd.dvd 5 t))
    (h : Dvd.dvd 5 (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t % 5 = 1 \/ 5 % (2 * e + 1) = 0) := by
  sorry

end OddPerfectNumber.Kernel
