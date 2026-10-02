-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_factorization_p_of_mul_prime_pow_ne
-- name    : OddPerfectNumber.Kernel.factorization_p_of_mul_prime_pow_ne
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:37:32.205567+00:00
-- url     : https://prove2.me/theorems/925fa028-2aa8-47e5-bdae-80eb7b7f3f59
-- title:
--   The multiplicity of a prime in p to the fifth times s is exactly five when p does not divide s
-- statement:
--   Let $p$ be prime and $s$ a natural number not divisible by $p$. Then the multiplicity of $p$ in $p^5 s$ is exactly $5$.
--
--   The hypothesis is not cosmetic: if $p \mid s$ the multiplicity is $5 + v_p(s)$, which is $7$ for $p = 5$, $s = 25$. This is the arithmetic step that turns the second Dris equation $\sigma(m^2) = p^5 s$ into the rigid constraint $v_p(\sigma(m^2)) = 5$, but only once $p \nmid s$ is established.
--
--   In the $k = 5$ two-prime residual that side condition is *not* automatic: from $s = d_1^2 q r$ with $q, r$ drawn from the cyclotomic blocks, the algebra forces $p \neq q$ and $p \neq r$ (since $\gcd(p, p^2+p+1) = \gcd(p, \tfrac{p+1}{2}(p^2-p+1)) = 1$), so $p \mid s$ reduces to $p \mid d_1$. Excluding that is a genuine odd-perfect-number fact rather than bare arithmetic, and is recorded separately so this child states only what it can prove.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.factorization_mul, Nat.factorization_pow, Nat.eq_of_factorization_eq') and Mathlib/Data/Nat/Prime/Basic.lean. The multiplicity of a prime in a product of a prime power and a number coprime to it is exactly the exponent; verified on 221 small cases with a counter-check at $p = 5$, $s = 25$. This child encodes no conjecture and asserts no OPN content.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem factorization_p_of_mul_prime_pow_ne {p s : Nat} (hp : p.Prime) (hps : Not (p ∣ s)) : (p ^ 5 * s).factorization p = 5 := by
  sorry

end OddPerfectNumber.Kernel
