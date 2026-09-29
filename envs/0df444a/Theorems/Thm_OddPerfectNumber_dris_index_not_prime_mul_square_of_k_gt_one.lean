-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_index_not_prime_mul_square_of_k_gt_one
-- name    : OddPerfectNumber.dris_index_not_prime_mul_square_of_k_gt_one
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T22:59:30.440955+00:00
-- url     : https://prove2.me/theorems/a8d543b9-420f-4803-9abb-51602784e78a
-- title:
--   Dris index is not a prime times a square
-- statement:
--   Let $p$ be a prime with $p \equiv 1 \pmod 4$, $k \equiv 1 \pmod 4$ with $k > 1$, $m$ odd with $p \nmid m$, and suppose the two Dris identities $2m^2 = \sigma(p^k) s$ and $\sigma(m^2) = p^k s$ both hold. Then the index $s$ is not a prime times a square, i.e. there are no $q$ prime and $a$ with $s = q\,a^2$. This is the Dris-index form of Hirakawa's Theorem 1.1(2): for an odd perfect number $N = n^2 q^\alpha$ with $\alpha > 1$, $\sigma(n^2)/q^\alpha$ is neither a square nor a square times a prime, together with his Theorem 2.2 (no solution of $\sigma(q^\alpha) = 2\ell n^2$ for $\alpha > 3$, $q \equiv 1 \pmod 4$, $\ell$ prime). It is the step that forces the square-free part of the Dris index to have at least two distinct prime factors.
-- source:
--   Hirakawa, 'A note on the Diophantine equation $2\ell n^2 = 1 + q + \cdots + q^\alpha$ and application to odd perfect numbers', Indagationes Mathematicae 35 (2024) 282-287, Theorem 1.1(2) together with Theorems 2.1-2.2; specialised to the Dris parametrisation $N = p^k m^2$. Restated for the odd-perfect-number mission as the index exclusion that the square-free part of $s$ is neither $1$ nor a single prime.

import Mathlib

namespace OddPerfectNumber

theorem dris_index_not_prime_mul_square_of_k_gt_one (p k m s : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hkgt : 1 < k)
    (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) :
    ¬ ∃ q a, q.Prime ∧ s = q * a ^ 2 := by
  sorry

end OddPerfectNumber
