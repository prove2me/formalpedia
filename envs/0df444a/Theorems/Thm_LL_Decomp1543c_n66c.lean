-- Prove2me | Theorems.Thm_LL_Decomp1543c_n66c
-- name    : LL_Decomp1543c.n66c
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:36:28.721513+00:00
-- url     : https://prove2.me/theorems/381f6b4d-93db-4896-9b26-475c4e93466d
-- title:
--   Lemma 6.6 numerics, third term
-- statement:
--   For natural $N,q$ with $L=\log N\ge3100$ and $(0.28/1.0012)^2L^4<q<(1.0012/0.09)^2N/L^5$, $U=N^{2/5}L^{-4/5}$ and $V=N^{2/5}L^{1/5}$, one has $5(N/q)\log^2(UV)\le0.0131\,(N/\sqrt q)\,L^2$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.6. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_Uf
import Definitions.Def_LL_Decomp1543c_Vf

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem n66c (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) ≤
      0.0131 * N / √q * Real.log N ^ 2 := by sorry
end LL_Decomp1543c
