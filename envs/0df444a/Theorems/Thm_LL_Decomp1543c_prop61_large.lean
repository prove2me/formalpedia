-- Prove2me | Theorems.Thm_LL_Decomp1543c_prop61_large
-- name    : LL_Decomp1543c.prop61_large
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:37:08.617205+00:00
-- url     : https://prove2.me/theorems/ff4e27a3-f61b-446a-8cf5-98a76832da49
-- title:
--   Proposition 6.1 for $\log N\ge3100$
-- statement:
--   For real $c\ge0$ and $\alpha$, integer $a$ and natural $N,q$ with $\operatorname{Dioph}(\alpha,a,q)$, that is $q\ge1$, $\gcd(a,q)=1$, $|\alpha-a/q|\le q^{-2}$, and with $L=\log N\ge3100$ and $(0.28/1.0012)^2L^4<q<(1.0012/0.09)^2N/L^5$, one has $|S_\Lambda(c,N,\alpha)|\le0.28\,(N/\sqrt q)L^2+4N^{4/5}L^{1.4}+0.09\sqrt N\sqrt q\,L^{2.5}$, where $S_\Lambda(c,N,\alpha)=\sum_{1\le n\le N,\ cN<n}\Lambda(n)e(\alpha n)$. In the lab this is proved conditional on the open items here and on open leaves of Decomp1543a and Decomp1543b.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 168, Proposition 6.1, (6.2), in the range (6.3). https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_Dioph

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem prop61_large (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ)
    (q : ℕ) (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 0.28 * N / √q * Real.log N ^ 2 +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.09 * √N * √q * Real.log N ^ (2.5 : ℝ) := by sorry
end LL_Decomp1543c
