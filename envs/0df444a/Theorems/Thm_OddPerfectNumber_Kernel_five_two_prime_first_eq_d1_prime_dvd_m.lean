-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_first_eq_d1_prime_dvd_m
-- name    : OddPerfectNumber.Kernel.five_two_prime_first_eq_d1_prime_dvd_m
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T06:25:48.267261+00:00
-- url     : https://prove2.me/theorems/28ef75d8-d19a-4b4f-a57e-c1984c34a096
-- title:
--   In the k=5 two-prime branch every prime dividing d1 also divides m
-- statement:
--   Let p be a prime that is 1 modulo 4 with p not dividing m, let q < r be primes, and suppose the first k=5 Dris equation holds in its factored cyclotomic form. Then every prime dividing d1 also divides m. Indeed the equation rewrites as m^2 equal to the product of (p^2+p+1), ((p+1)/2 times (p^2-p+1)), d1^2 and q r, so d1 squared divides m squared and primality transfers the divisibility prime by prime. This shows the free square parameter of the first equation is not independent of m: its prime support lies inside the support of m, which is what makes the second Dris equation self-referential.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_first_eq_d1_prime_dvd_m {p m d1 q r : Nat} (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    forall t : Nat, t.Prime -> Dvd.dvd t d1 -> Dvd.dvd t m := by
  sorry

end OddPerfectNumber.Kernel
