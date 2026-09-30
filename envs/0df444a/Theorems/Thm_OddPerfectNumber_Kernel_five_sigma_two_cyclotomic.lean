-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_sigma_two_cyclotomic
-- name    : OddPerfectNumber.Kernel.five_sigma_two_cyclotomic
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-29T13:19:41.097856+00:00
-- url     : https://prove2.me/theorems/4817a3e7-bf86-46a2-9a93-c33798aadb0e
-- title:
--   For k=5 the Dris index equation factors into the two cyclotomic terms
-- statement:
--   For every natural number $p$, $2 \cdot (p^2+p+1) \cdot \left(\frac{p+1}{2}\right)(p^2-p+1) = \sigma(p^5)$. This is the exact factorisation of the first Dris equation on the $k=5$ branch: writing $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$ gives $\sigma(p^5) = 2UV$, so that equation reads $m^2 = d^2 \cdot (qUV)$ once $m^2 = d^2 x$ is cancelled. The identity is a polynomial one, since $\sigma(p^5) = 1+p+\dots+p^5 = (1+p+p^2)(1+p^3)$; no oddness assumption on $p$ is required, and the division by $2$ is exact for every $p$ because $(p+1)(p^2-p+1) = p^3+1$.
-- source:
--   Mathlib/NumberTheory/Divisors.lean (`sum_divisors_prime_pow`, the additive form of `prod_divisors_prime_pow` at line 516) rewrites the divisor sum over $(p^5)$.divisors as a sum over `range 6`, after which `ring` proves the polynomial identity. The factorisation is the standard one $1+x+\dots+x^5 = (1+x+x^2)(1+x^3)$.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_sigma_two_cyclotomic (p : Nat) :
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d := by
  sorry

end OddPerfectNumber.Kernel
