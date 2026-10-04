-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_dvd
-- name    : OddPerfectNumber.Kernel.five_two_prime_index_dvd
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-01T12:04:33.168806+00:00
-- url     : https://prove2.me/theorems/004189f2-03ac-423a-9205-fd8eb711b622
-- title:
--   Every prime dividing the k=5 index divides the cyclotomic product
-- statement:
--   Let p be a prime congruent to 1 modulo 4, m an odd natural number not divisible by p, and q and r primes. Suppose the k=5 Dris equation 2 m squared equals sigma of p to the fifth times d1 squared q r in its already factorised form. Then every prime dividing the index d1 squared q r also divides the cyclotomic product (p+1)/2 times p squared plus p plus one times p squared minus p plus one. Equivalently, the squarefree kernel of that cyclotomic product is contained in the set of primes dividing the index. Since the index has squarefree kernel exactly the two primes q and r, this forces the squarefree kernel of the cyclotomic product to have at most two prime factors, which for all but two Euler primes up to fifteen hundred fails.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_index_dvd {p m d1 q r : Nat} (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hq : q.Prime) (hr : r.Prime)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (hm0 : m != 0) :
    ∀ t, Dvd.dvd t (d1 ^ 2 * (q * r)) ->
      Dvd.dvd t ((p + 1) / 2 * (p ^ 2 + p + 1) * (p ^ 2 - p + 1)) := by
  sorry

end OddPerfectNumber.Kernel
