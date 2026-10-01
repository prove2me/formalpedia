-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_no_two_prime_squarefree_index
-- name    : OddPerfectNumber.Kernel.five_no_two_prime_squarefree_index
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T14:10:39.205009+00:00
-- url     : https://prove2.me/theorems/6eb10265-4d2f-4227-b550-4a6ccf0d94b3
-- title:
--   The $k = 5$ Dris index is not a product of two distinct primes times a square
-- statement:
--   There are no natural numbers $p, m, d_1, q, r$ with $p$ a prime congruent to $1$ modulo $4$, $m$ odd, $p \nmid m$, $q < r$ both prime, $d_1 \ge 0$, such that both $k = 5$ Dris equations hold with the index $s = d_1^2 q r$.
--
--   The first equation is written in the already-factorised form of $\sigma(p^5) = 2(p^2+p+1)\left(\frac{p+1}{2}\right)(p^2-p+1)$, the factorisation proved in `OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd_prime` (7f2041ff-30b4-4c8d-ad98-798dc15b91e1). The second equation keeps its natural sum-of-divisors form, which no proved factorisation is available for.
--
--   This is the genuine research residual of the $k = 5$ branch and it is the step that cannot be taken from the first equation alone. Indeed $p = 5$, $s = 217 = 7 \cdot 31$, $m = 651$ satisfies $2m^2 = \sigma(5^5) s$ exactly, with $U = p^2+p+1 = 31$ and $V = \frac{p+1}{2}(p^2-p+1) = 63 = 7 \cdot 3^2$, so $sUV = 651^2$; the configuration is a genuine two-prime square-free kernel satisfying the whole first Dris equation. It is excluded only by the second equation, since $\sigma(651^2) = 735813$ while $5^5 \cdot 217 = 678125$. Any proof of this target must therefore use the second Dris equation essentially, through the divisor-sum support of $m^2$, the incoming sources of $q$ and $r$, or multiplicative-order and valuation constraints.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_no_two_prime_squarefree_index (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime)
    (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    False := by
  sorry

end OddPerfectNumber.Kernel
