-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_sigma_two_cyclotomic_odd
-- name    : OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-29T13:25:47.860677+00:00
-- url     : https://prove2.me/theorems/789ef82d-9770-49cc-ab14-759c2a9e477a
-- title:
--   For odd p the k=5 divisor sum factors into the two cyclotomic terms
-- statement:
--   For every odd natural number $p$, $2 \cdot (p^2+p+1) \cdot \left(\frac{p+1}{2}\right)(p^2-p+1) = \sigma(p^5)$. This is the exact factorisation of the first Dris equation on the $k=5$ branch: writing $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$ gives $\sigma(p^5) = 2UV$, so that equation reads $m^2 = d^2 \cdot (qUV)$ once the explicit square factor is cancelled. The identity is the polynomial one $\sigma(p^5) = 1+p+\dots+p^5 = (1+p+p^2)(1+p^3)$, and the oddness hypothesis is exactly what makes the `Nat` division $(p+1)/2$ exact rather than a truncation. The hypothesis is not cosmetic: for even $p$ the `Nat` quotient truncates and the identity fails, for instance $p=4$ gives $1092 \neq 1365$.
-- source:
--   Mathlib/NumberTheory/Divisors.lean (`sum_divisors_prime_pow`, the additive form of `prod_divisors_prime_pow` at line 516) rewrites the divisor sum over $(p^5)$.divisors as a sum over `range 6`, after which the polynomial identity is closed over `Z` and transferred back to `Nat`. The factorisation is the standard one $1+x+\dots+x^5 = (1+x+x^2)(1+x^3)$, and $(p+1)(p^2-p+1) = p^3+1$.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_sigma_two_cyclotomic_odd (p : Nat) (hp : Odd p) :
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d := by
  sorry

end OddPerfectNumber.Kernel
