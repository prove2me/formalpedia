-- Prove2me | Theorems.Thm_LL_Decomp1543c_n65b
-- name    : LL_Decomp1543c.n65b
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:34:41.322286+00:00
-- url     : https://prove2.me/theorems/596849cf-70f0-4e89-85c0-4ba0f206341e
-- title:
--   Lemma 6.5 numerics, second term
-- statement:
--   For natural $N,q$ with $L=\log N\ge3100$ and $(0.28/1.0012)^2L^4<q<(1.0012/0.09)^2N/L^5$ and $V=N^{2/5}L^{1/5}$, one has $V\log q\,\log N\le0.0001\,N^{4/5}L^{1.4}$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.5. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_Vf

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem n65b (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Vf N * Real.log q * Real.log N ≤ 0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by sorry
end LL_Decomp1543c
