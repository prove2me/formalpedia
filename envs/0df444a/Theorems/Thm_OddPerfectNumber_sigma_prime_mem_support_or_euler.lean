-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_prime_mem_support_or_euler
-- name    : OddPerfectNumber.sigma_prime_mem_support_or_euler
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T10:15:31.02856+00:00
-- url     : https://prove2.me/theorems/0519f1c5-56fb-4423-92dc-f924a643690e
-- title:
--   A prime divisor of the square-part sigma sum is Euler or supported
-- statement:
--   Let $p$ and $r$ be primes. Suppose a square divisor sum satisfies $\sigma(m^2)=p d$, the cofactor $d$ divides $m^2$, and $r$ divides $\sigma(m^2)$. Then either $r=p$, or $r$ divides $m$. Thus every prime divisor of the square-part sigma sum other than the Euler prime is already in the support of the square cofactor. This is the elementary support-closure rule used in Euler-form odd-perfect-number factor chains.
-- source:
--   Derived elementary support consequence of the canonical Dris relation sigma(m^2) = p*d and d | m^2 in the Odd Perfect Number Conjecture mission; uses only primality and divisibility.

import Mathlib

namespace OddPerfectNumber

theorem sigma_prime_mem_support_or_euler (p m d r : Nat)
    (hp : p.Prime) (hr : r.Prime)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hrsigma : r ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    r = p ∨ r ∣ m := by sorry

end OddPerfectNumber
