-- Prove2me | Theorems.Thm_LL_Decomp1543c_n66b
-- name    : LL_Decomp1543c.n66b
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:36:02.633996+00:00
-- url     : https://prove2.me/theorems/dc7882bf-0fb0-4810-9a2d-c9f5988dab60
-- title:
--   Lemma 6.6 numerics, second term
-- statement:
--   For natural $N,q$ with $L=\log N\ge3100$ and $(0.28/1.0012)^2L^4<q<(1.0012/0.09)^2N/L^5$, $U=N^{2/5}L^{-4/5}$ and $V=N^{2/5}L^{1/5}$, one has $UV\log q\,\log(UV)\le0.8\,N^{4/5}L^{1.4}$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.6. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_Uf
import Definitions.Def_LL_Decomp1543c_Vf

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem n66b (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) ≤
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by sorry
end LL_Decomp1543c
