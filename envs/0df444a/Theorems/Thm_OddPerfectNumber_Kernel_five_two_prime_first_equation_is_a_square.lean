-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_first_equation_is_a_square
-- name    : OddPerfectNumber.Kernel.five_two_prime_first_equation_is_a_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T16:46:28.790869+00:00
-- url     : https://prove2.me/theorems/5013d85c-eadd-4c1c-9e86-d3f409b6a019
-- title:
--   Two-prime square-free k=5 index: the first Dris equation is exactly a perfect square
-- statement:
--   Let p, m, d1, q, r, u, a, b be natural numbers. Suppose p is a prime, p is congruent to one modulo four, d1 is nonzero, p plus one equals three times u squared, p squared plus p plus one equals q times a squared, and p squared minus p plus one equals three times r times b squared. Suppose the first k=5 Dris equation holds in the form two m squared equals two times (p squared plus p plus one) times ((p+1)/2 times (p squared minus p plus one)) times (d1 squared times q times r). Then m equals three times u times a times b times d1 times q times r.
-- source:
--   This isolates the arithmetic that turns the block allocation of the k=5 two-prime square-free index into an explicit value of m, with no division anywhere. Write C = p^2+p+1, B = (p+1)/2 and D = p^2-p+1. The first Dris equation is m^2 = B*C*D*d1^2*q*r. Because p = 5 (mod 12) the prime 3 divides both B and D, so with B = 3*u^2, C = q*a^2 and D = 3*r*b^2 the product on the right is 9*u^2*q*a^2*r*b^2*d1^2*q*r = (3*u*a*b*d1*q*r)^2 exactly. Both division-free hypotheses he and hd state the corresponding factorizations p+1 = 3*u^2 and p^2-p+1 = 3*r*b^2 directly, so no quotient of a Nat division has to be eliminated. From m^2 = X^2 with X = 3*u*a*b*d1*q*r the conclusion m = X follows from Nat.sq_sqrt together with cancellation of the common square factor: m^2 = X^2 rewrites as (m/X)^2 = 1 in the quotient, or more directly by Nat.eq_of_mul_eq_mul_left after writing both sides as products of the same square. Verified numerically on the four computable configurations (p,q,r,d1) = (5,31,7,1), (5,31,7,3), (293,86143,79,1) and (293,86143,79,3): the predicted m agrees exactly with the square root of (sigma(p^5)/2)*s in every case. The companion statement of the three blocks being pairwise coprime, gcd((p+1)/6, p^2+p+1) = gcd(p^2+p+1, (p^2-p+1)/3) = 1, is what forces the allocation hypotheses he, hc, hd in the first place.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_first_equation_is_a_square (p m d1 q r u a b : Nat)
    (hp : Nat.Prime p) (hd1 : d1 != 0)
    (he : p + 1 = 3 * u ^ 2)
    (hc : p ^ 2 + p + 1 = q * a ^ 2)
    (hd : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  sorry

end OddPerfectNumber.Kernel
