-- Prove2me | Theorems.Thm_LL_Decomp1543c_n65a
-- name    : LL_Decomp1543c.n65a
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:34:13.961599+00:00
-- url     : https://prove2.me/theorems/309ba694-761e-4677-80a5-b2137389f039
-- title:
--   Lemma 6.5 numerics, first term
-- statement:
--   For natural $N,q$ with $L=\log N\ge3100$ and $(0.28/1.0012)^2L^4<q<(1.0012/0.09)^2N/L^5$, one has $(5q+1.5\,q\log q)\log N\le0.0006\sqrt N\sqrt q\,L^{2.5}$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.5. https://doi.org/10.4064/aa105-2-3

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem n65a (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log N ≤
      0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by sorry
end LL_Decomp1543c
