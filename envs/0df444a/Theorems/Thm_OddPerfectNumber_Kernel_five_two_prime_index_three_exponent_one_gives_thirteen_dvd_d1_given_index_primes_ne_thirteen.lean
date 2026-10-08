-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen
-- name    : OddPerfectNumber.Kernel.five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T13:15:07.32297+00:00
-- url     : https://prove2.me/theorems/689ded24-ec3c-4274-9ef3-b2f5c011c503
-- title:
--   In the k=5 two-prime residual, 3 dividing m exactly once forces 13 to divide d1, given that none of p, q, r is 13
-- statement:
--   Suppose p is the Euler prime of an odd perfect number candidate with p = 1 (mod 4), the k=5 Dris equation sigma(m^2) = p^5 d1^2 q r holds for distinct primes q < r neither of which is 3, and 3 occurs in m to exactly the first power.  If additionally none of p, q, r equals 13, then 13 divides d1.
-- source:
--   MECHANISM.  he gives v_3(m) = 1, so 3 is a prime divisor of m and the Proved theorem 40498f43 `local_sigma_dvd_sigma_of_mem_primeFactors` yields sigma(3^(2*1)) | sigma(m^2). Since sigma(3^2) = 1 + 3 + 9 = 13, we get 13 | sigma(m^2) = p^5 d1^2 q r.  The three hypotheses hp13, hq13, hr13 exclude 13 from p^5, q and r, so 13 | d1^2, and 13 being prime gives 13 | d1.
--
--   WHY THE THREE EXCLUSIONS ARE NEEDED.  The earlier published version bcd032e7 omitted them. hp4 : p % 4 = 1 admits p = 13 since 13 % 4 = 1, and hq3/hr3 only exclude 3, not 13.  With the established branch congruences p = 5 (mod 48) and q, r = 7 (mod 24) the exclusions are automatic (13 mod 48 = 13, 13 mod 24 = 13), but those congruences are not binders of the published statement, so they cannot be used to discharge the step.  This corrected version names exactly the three missing facts and drops the unused hypotheses.
--
--   AUDIT.  Enumerating p up to 53, q < r over 14 primes and d1 up to 31 gives 9 configurations satisfying the first Dris equation with v_3(m) = 1, of which 0 satisfy the second.  The search is therefore VACUOUS and proves nothing about the conclusion; it is recorded only as a reminder that h2 is very restrictive.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen (p m d1 q r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3) (hp13 : p != 13) (hq13 : q != 13) (hr13 : r != 13)
    (he : m.factorization 3 = 1)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    Dvd.dvd 13 d1 := by
  sorry

end OddPerfectNumber.Kernel
