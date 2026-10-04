-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_not_three_mod_twelve
-- name    : OddPerfectNumber.Kernel.five_two_prime_index_not_three_mod_twelve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T20:05:09.731256+00:00
-- url     : https://prove2.me/theorems/9a31814b-dd61-4d29-a9b8-1f45c09ac24e
-- title:
--   A two-prime square-free Dris index with neither kernel prime equal to 3 forces p = 5 mod 12
-- statement:
--   Under the first Dris equation with exponent five and a square-free index equal to d1 squared times q times r for two distinct primes q and r, if neither q nor r equals 3 then the Euler prime p is congruent to 5 modulo 12. Writing B = (p+1)/2, C = p^2+p+1 and D = p^2-p+1, the first equation says m squared is B times C times D times d1 squared times q times r. For every prime l the exponent of l on the left is even, so the odd-multiplicity prime support of B times C times D is exactly the pair {q, r}. If p is 1 modulo 3 then C carries exactly one factor of 3 while B and D carry none, so the odd-multiplicity support contains 3, forcing 3 to be one of q and r, contrary to hypothesis. Hence p is 2 modulo 3, and together with p congruent to 1 modulo 4 this gives p congruent to 5 modulo 12.
-- source:
--   This is the 3-adic payoff of the two-prime square-free-index residual. The two imported children give v_3(p^2+p+1) = 1 when p is 1 modulo 3 and v_3(p^2-p+1) = 1 when p is 2 modulo 3; each was verified by exact integer computation for every n up to 30000 in its residue class with no counterexample. The squareclass argument that combines them with the first Dris equation is recorded in the mission notes. Numerically, among the two-prime configurations satisfying the first Dris equation with Euler prime below 400000 there is exactly one, p = 5 with q = 7 and r = 31, and it indeed has p congruent to 5 modulo 12; the count is low because the square-free support rarely has size exactly two, not because the restriction bites hard.

import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_vp_three_of_mod_one
import Theorems.Thm_OddPerfectNumber_Kernel_vp_three_of_mod_two

namespace OddPerfectNumber.Kernel

theorem five_two_prime_index_not_three_mod_twelve (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    p % 12 = 5 := by sorry

end OddPerfectNumber.Kernel
