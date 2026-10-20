-- Prove2me | Theorems.Thm_Helfgott_vonMangoldt_sq_le_log_mul_psi
-- name    : Helfgott.vonMangoldt_sq_le_log_mul_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T19:02:31.873667+00:00
-- url     : https://prove2.me/theorems/ce94e6aa-148b-443d-bde7-d2c42dccb53b
-- title:
--   $\sum_{n\le X}\Lambda(n)^2 \le \log X\cdot\psi(X)$
-- statement:
--   For every natural number $X \\ge 2$, the sum over the von Mangoldt squares up to $X$ is controlled log-weighted by Chebyshev's $\\psi$:
--
--   $$\\sum_{n \\le X} \\Lambda(n)^2 \\;\\le\\; (\\log X)\\, \\psi(X),$$
--
--   where $\\psi(X) = \\sum_{n \\le X} \\Lambda(n)$.
--
--   **Proof idea.** Since $\\Lambda(n) = \\log p$ when $n = p^k$ and vanishes otherwise, each term satisfies $\\Lambda(n) \\le \\log n \\le \\log X$, so each square drops to $\\Lambda(n)\\cdot\\Lambda(n) \\le \\Lambda(n)\\log X$, and the bound follows by summation. This is the Parseval-side arithmetic backbone for the $\\Lambda^2$-energy steps in the `Helfgott` circle-method development: squared-coefficient sums are demanded by any $L^2$ estimate on a weighted prime exponential sum.
--
--   **Formalization Note.** Entirely finite range `Finset.Icc 0 X`; no analytic input. Uses `ArithmeticFunction.vonMangoldt_le_log` and the `Chebyshev.psi_eq_sum_Icc` characterization.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes; used in the L^2 Parseval block of the Helfgott minor-arc estimate on this platform.

import Mathlib

namespace Helfgott

theorem vonMangoldt_sq_le_log_mul_psi (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ Finset.Icc 0 X, (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
      Real.log X * Chebyshev.psi X := by sorry

end Helfgott
