-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_index_not_prime_mul_square
-- name    : OddPerfectNumber.Kernel.five_index_not_prime_mul_square
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T14:17:10.532933+00:00
-- url     : https://prove2.me/theorems/2ec27119-2f77-425b-ab15-a95e11c2f9bc
-- title:
--   The k=5 Dris index is not a prime times a square
-- statement:
--   On the $k=5$ branch of the Dris conjecture, the index $s$ of the second equation cannot be a prime times a square. This is the elementary replacement for the deep quadratic-order consequence of Hirakawa, and it needs only the first Dris equation. Writing $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$, one has $\sigma(p^5) = 2UV$, so $2m^2 = 2UVqa^2$ gives $m^2 = a^2(qUV)$; cancelling the square factor $a^2$ forces $qUV$ to be a square. But $U$ and $V$ are coprime and both are non-squares (children `five_cyclotomic_pair_coprime` and `five_cyclotomic_factors_ne_square`), so each supplies a prime of odd multiplicity, those primes are distinct, and the single prime $q$ cannot repair both. Hence `q * U * V` is not a square, a contradiction. The unused hypotheses $hp4$ and $hpm$ are retained so the statement matches the parent Dris setting exactly.
-- source:
--   Hirakawa, Indagationes Mathematicae 35 (2024), Theorem 1.1(2), supplies this for general $k$ only through quadratic orders and generalised Fermat theory. For $k=5$ it is elementary parity. The three inputs are the accepted children: `five_sigma_two_cyclotomic_odd` (the exact factorisation $\sigma(p^5)=2UV$), `isSq_of_sq_mul_eq_sq` (cancelling the explicit square factor), and `prime_mul_coprime_nonsquares_not_square` (one prime cannot repair two distinct odd prime exponents).

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_index_not_prime_mul_square (p m s q a : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hs : s = q * a ^ 2) (hspos : 0 < s)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s) :
    False := by
  sorry

end OddPerfectNumber.Kernel
