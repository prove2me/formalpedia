-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_prime_mul_coprime_nonsquares_not_square
-- name    : OddPerfectNumber.Kernel.prime_mul_coprime_nonsquares_not_square
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T06:55:55.847119+00:00
-- url     : https://prove2.me/theorems/0a9fa825-491c-44a2-9f99-eaf3e4677c74
-- title:
--   A prime times two coprime non-squares is not a square
-- statement:
--   Let $a$ and $b$ be nonzero natural numbers with $a$ coprime to $b$, neither of which is a perfect square, and let $q$ be prime. Then $q \cdot a \cdot b$ is not a perfect square. Equivalently: a prime times a product of two coprime non-squares is never a square. This is the elementary parity-toggling fact that replaces the deep quadratic-order input of Hirakawa on the $k=5$ branch of the Odd Perfect Number Conjecture. Coprimality guarantees that $a$ and $b$ each supply a prime of odd multiplicity, and that the two primes are distinct; the single extra factor $q$ can repair the parity at only one of them, so an odd multiplicity survives.
-- source:
--   Hirakawa, Indagationes Mathematicae 35 (2024), Theorem 1.1(2), supplies this conclusion for general k by deep quadratic-order and generalised-Fermat machinery. For k=5 the same conclusion is elementary: sigma(p^5)/2 = (p^2+p+1) * (((p+1)/2)(p^2-p+1)) is a product of two coprime non-squares, so the one-prime square-free kernel case is impossible by parity alone. The two cyclotomic children Kernel.five_cyclotomic_factors_ne_square (648a7dc4) and Kernel.five_cyclotomic_pair_coprime (dbed225d) supply the two non-square and coprimality hypotheses.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem prime_mul_coprime_nonsquares_not_square {a b q : Nat}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a.Coprime b)
    (hna : ¬ ∃ y, y ^ 2 = a) (hnb : ¬ ∃ y, y ^ 2 = b) (hq : q.Prime) :
    ¬ ∃ y, y ^ 2 = q * a * b := by
  sorry

end OddPerfectNumber.Kernel
