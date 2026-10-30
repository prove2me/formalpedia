-- Prove2me | Theorems.Thm_LL_Decomp1543a_squarefree_dyadic
-- name    : LL_Decomp1543a.squarefree_dyadic
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:41:55.63693+00:00
-- url     : https://prove2.me/theorems/ff574a7f-d99c-4a21-88b1-9acb0f337185
-- title:
--   Explicit squarefree count on a dyadic block
-- statement:
--   For every natural $N$ and real $M\ge\exp(13.066)$, $\sum_{t\in T(N,M)}|\mu(t)|\le0.6111M$. Thus the count is restricted to $1\le t\le N$ as well as $M<t\le2M$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 173, equation 6.20. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_tBlock

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem squarefree_dyadic (N : ℕ) (M : ℝ) (hM : exp 13.066 ≤ M) :
    ∑ t ∈ tBlock N M, |(moebius t : ℝ)| ≤ 0.6111 * M := by sorry
end LL_Decomp1543a
