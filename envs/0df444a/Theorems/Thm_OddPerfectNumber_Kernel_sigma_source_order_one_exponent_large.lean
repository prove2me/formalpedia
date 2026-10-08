-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sigma_source_order_one_exponent_large
-- name    : OddPerfectNumber.Kernel.sigma_source_order_one_exponent_large
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T03:04:27.937611+00:00
-- url     : https://prove2.me/theorems/d7dcfa98-a917-4ece-887c-d2edac80c88f
-- title:
--   An incoming sigma source of the Euler prime congruent to 1 modulo p carries an exponent at least (p-1)/2 in the Dris square
-- statement:
--   Let p and t be primes with p not dividing t, and suppose the geometric sum sigma(t^(2e)) = 1 + t + ... + t^(2e) is divisible by p. If in addition p divides t - 1, so that t is congruent to 1 modulo p and the multiplicative order of t modulo p is 1, then the exponent e must be large: 2e + 1 is a positive multiple of p, so (p - 1) / 2 <= e. Equivalently, an incoming sigma source of the Euler prime whose order modulo p is 1 must appear in the Dris square with exponent at least (p - 1)/2, which for any fixed p is a very large exponent. This bounds the order-1 branch of the sigma-source budget, complementing the fact that an order greater than 1 must divide (p - 1) / 4.
-- source:
--   Elementary modular arithmetic. Since p | t - 1 we have t = 1 (mod p), so every term t^i is 1 (mod p) and the sum over i in range (2e+1) is congruent to 2e + 1 (mod p). The divisibility hypothesis therefore gives p | 2e + 1; since 2e + 1 is positive this forces p <= 2e + 1, which is exactly the stated bound. No deep number theory is involved; this is the order-one branch of the local sigma valuation budget in the k = 5 two-prime Dris residual.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sigma_source_order_one_exponent_large {p t e : Nat} (hp : p.Prime)
    (ht : t.Prime)
    (hpt : Not (Dvd.dvd p t))
    (hord : Dvd.dvd p (t - 1))
    (h : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (p - 1) / 2 <= e := by
  sorry

end OddPerfectNumber.Kernel
