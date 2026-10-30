-- Prove2me | Theorems.Thm_LL_Decomp1543a_S4_dyadic
-- name    : LL_Decomp1543a.S4_dyadic
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:41:25.345656+00:00
-- url     : https://prove2.me/theorems/b3055a82-e46e-4953-8285-2d02c13fe8b1
-- title:
--   Dyadic decomposition of the fourth Vaughan sum
-- statement:
--   For every real $c,\alpha$, natural $N$ and positive real $U,V$, $S_{\Lambda_4(U,V,\cdot)}(c,N,\alpha)=\sum_{0\le j<J(N,U,V)}B(c,N,U,2^jV,\alpha)$. No additional hypothesis $UV\le N$ is present.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, equations 6.10 and 6.11. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_rangeN
import Definitions.Def_LL_Decomp1543a_Ssum
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_lam4
import Definitions.Def_LL_Decomp1543a_tBlock
import Definitions.Def_LL_Decomp1543a_mRange
import Definitions.Def_LL_Decomp1543a_inner
import Definitions.Def_LL_Decomp1543a_block
import Definitions.Def_LL_Decomp1543a_Jn

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem S4_dyadic (c : ℝ) (N : ℕ) (U V α : ℝ) (hU : 0 < U) (hV : 0 < V) :
    Ssum (lam4 U V) c N α = ∑ j ∈ range (Jn N U V), block c N U (2 ^ j * V) α := by sorry
end LL_Decomp1543a
