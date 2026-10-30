-- Prove2me | Theorems.Thm_LL_Decomp1543c_n65c
-- name    : LL_Decomp1543c.n65c
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:35:13.652367+00:00
-- url     : https://prove2.me/theorems/6f0f3d1a-f2b2-45e3-9da1-ea96a2433d29
-- title:
--   Lemma 6.5 numerics, third term
-- statement:
--   For natural $N,q$ with $L=\log N\ge3100$ and $(0.28/1.0012)^2L^4<q<(1.0012/0.09)^2N/L^5$ and $V=N^{2/5}L^{1/5}$, one has $5(N/q)\log V\,\log N\le0.0282\,(N/\sqrt q)\,L^2$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.5. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_Vf

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem n65c (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Vf N) * Real.log N ≤ 0.0282 * N / √q * Real.log N ^ 2 := by sorry
end LL_Decomp1543c
