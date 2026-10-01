-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_cyclotomic_primes_dvd_m
-- name    : OddPerfectNumber.Kernel.five_two_prime_cyclotomic_primes_dvd_m
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:20:14.635755+00:00
-- url     : https://prove2.me/theorems/13f23023-b5ec-4902-9b88-c03981f04b0b
-- title:
--   In the k=5 two-prime case both cyclotomic kernel primes divide m
-- statement:
--   Let $p \equiv 1 \pmod 4$ be an odd prime, let $q < r$ be primes, and suppose the $k=5$ first Dris relation holds with square-free kernel $d_1^2 q r$. Assume in addition that $q r (p^2+p+1) \frac{p+1}{2}(p^2-p+1)$ is a perfect square. Then both $q$ and $r$ divide $m$.
--
--   The accepted child `five_two_prime_cyclotomic_split` (81a70179) shows that the cyclotomic block $U = p^2+p+1$ is $q x^2$ or $r x^2$, and the same parity argument applied to $V$ gives $V = t y^2$ for the remaining kernel prime $t$. Substituting into the square relation $m^2 = d_1^2 U V q r$ gives $m^2 = d_1^2 q^2 r^2 x^2 y^2$, hence $m = d_1 q r x y$, so $q \mid m$ and $r \mid m$.
--
--   This is the first structural bridge from the parity split into the second Dris equation: it shows that each kernel prime must be supplied to $\sigma(m^2)$ by a different prime factor of $m$, since $\sigma(q^{2a}) \equiv 1 \pmod q$.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.eq_of_factorization_eq', Nat.factorization_eq_zero_of_not_dvd) together with the accepted children OddPerfectNumber.Kernel.five_two_prime_cyclotomic_split (81a70179-c0e7-41e8-97bd-86af2cb90f91), OddPerfectNumber.Kernel.two_prime_block_is_prime_mul_sq (672c3afb) and OddPerfectNumber.Kernel.isSq_of_sq_mul_eq_sq (74779081). Pure exponent-parity bookkeeping; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_cyclotomic_primes_dvd_m (p m d1 q r : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (hsq : exists y : Nat, y ^ 2 = q * r * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) :
    q ∣ m ∧ r ∣ m := by
  sorry

end OddPerfectNumber.Kernel
