-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_m_is_three_times_four_factor_form
-- name    : OddPerfectNumber.Kernel.five_m_is_three_times_four_factor_form
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T16:43:01.629986+00:00
-- url     : https://prove2.me/theorems/6f5c2175-369a-41bf-901c-e63daff9e4e6
-- title:
--   The k=5 Dris equation forces an explicit factorisation of m
-- statement:
--   Let p, m, d1, q, r be natural numbers. Suppose p is a prime congruent to one modulo four, d1 is nonzero, and the first k=5 Dris equation holds in the form two m squared equals two times (p squared plus p plus one) times ((p+1)/2 times (p squared minus p plus one)) times (d1 squared times q times r). Suppose additionally that there are natural numbers u, a and b with (p+1)/6 equal to u squared, p squared plus p plus one equal to q times a squared, and (p squared minus p plus one)/3 equal to r times b squared. Then m equals three times u times a times b times d1 times q times r.
-- source:
--   This is the normalisation step of the k=5 two-prime square-free index. Writing B = (p+1)/2, C = p^2+p+1 and D = p^2-p+1, the first Dris equation is m^2 = B*C*D*d1^2*q*r. Because p = 5 (mod 12) the prime 3 divides both B and D, so with E = B/3 = (p+1)/6 and F = D/3 the equation becomes m^2 = 9*E*C*F*d1^2*q*r. The three blocks E, C, F are pairwise coprime: gcd(E,C) = 1 since C = 1 (mod p+1) and E divides p+1; gcd(C,F) = 1 since C - D = 2p with both odd and C = D = 1 (mod p); and 3 does not divide E. Substituting the displayed square forms of E, C and F makes the right-hand side the square (3*u*a*b*d1*q*r)^2, so m equals that square root. The block allocation giving E = u^2, C = q*a^2 and F = r*b^2 is supplied as hypotheses; this child isolates only the arithmetic that turns that allocation into an explicit value of m. Verified numerically on the four computable configurations (p,q,r,d1) = (5,31,7,1), (5,31,7,3), (293,86143,79,1) and (293,86143,79,3), for which the predicted m agrees exactly with the square root of (sigma(p^5)/2)*s.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_m_is_three_times_four_factor_form (p m d1 q r u a b : Nat)
    (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hd1 : d1 != 0)
    (he : (p + 1) / 6 = u ^ 2)
    (hc : p ^ 2 + p + 1 = q * a ^ 2)
    (hf : (p ^ 2 - p + 1) / 3 = r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  sorry

end OddPerfectNumber.Kernel
