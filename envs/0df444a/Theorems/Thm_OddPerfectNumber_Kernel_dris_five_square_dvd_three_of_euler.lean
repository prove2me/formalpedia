-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_dris_five_square_dvd_three_of_euler
-- name    : OddPerfectNumber.Kernel.dris_five_square_dvd_three_of_euler
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T22:21:19.752707+00:00
-- url     : https://prove2.me/theorems/bf2ae414-3fbb-4213-baeb-a0d527556aa9
-- title:
--   The first Dris equation at exponent five forces three to divide the square part
-- statement:
--   Let p, m and s be natural numbers with s nonzero, and suppose the first Dris equation at exponent five holds: twice the square of m equals the sum of the divisors of p to the fifth times s. Assume p is a prime different from two. Then three divides m, and therefore three divides m squared. Indeed the sum of the six terms one plus p plus p squared plus p cubed plus p to the fourth plus p to the fifth is always divisible by three when p is a prime other than three: if p is one modulo three all six terms are one modulo three, and if p is minus one modulo three the six terms alternate one and two and sum to nine, which is zero modulo three. Hence three divides twice the square of m; since three does not divide two and three is prime, three divides m squared and then three divides m. This is an unconditional consequence of the first Dris equation alone, with no hypothesis on the square-free structure of the index. Note that the corresponding claim for the index itself, that three divides s, is false: the three-adic valuation of the sum of the divisors of p to the fifth is not always one, for instance it is two when p is five.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem dris_five_square_dvd_three_of_euler (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hs : s != 0)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s) :
    Dvd.dvd 3 m := by
  sorry

end OddPerfectNumber.Kernel
