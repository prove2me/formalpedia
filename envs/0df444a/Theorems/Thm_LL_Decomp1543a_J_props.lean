-- Prove2me | Theorems.Thm_LL_Decomp1543a_J_props
-- name    : LL_Decomp1543a.J_props
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:51:55.414492+00:00
-- url     : https://prove2.me/theorems/573969cc-02b4-4aab-b352-f283a2ecbd62
-- title:
--   Endpoint and logarithmic bounds for the dyadic count
-- statement:
--   For natural $N$ and positive real $U,V$ satisfying $UV\le N$, let $J=J(N,U,V)$. Then $2^{J-1}V\le N/U$ and $J\le1+\log(N/(UV))/\log2$, with natural-number subtraction in $J-1$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, equation 6.10. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_Jn

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem J_props (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U * V ≤ N) :
    2 ^ (Jn N U V - 1) * V ≤ N / U ∧
      (Jn N U V : ℝ) ≤ 1 + Real.log (N / (U * V)) / Real.log 2 := by sorry
end LL_Decomp1543a
