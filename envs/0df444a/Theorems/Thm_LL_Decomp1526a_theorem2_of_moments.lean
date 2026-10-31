-- Prove2me | Theorems.Thm_LL_Decomp1526a_theorem2_of_moments
-- name    : LL_Decomp1526a.theorem2_of_moments
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:09:03.584608+00:00
-- url     : https://prove2.me/theorems/79c92e2b-636e-4069-8a34-9fc4c418de87
-- title:
--   Theorem 2 from a first and a second moment
-- statement:
--   Let $L,U$ be real numbers with $L>0$, $U>0$ and $1/5\le L^2/U$. Suppose that for every real $X\ge e^{67}$, $LX^2\le\sum_{N}r(N)$ and $\sum_N r(N)^2\le UX^3$, where $N$ ranges over the even natural numbers with $\lfloor X\rfloor<N\le\lfloor 2X\rfloor$. Then Theorem 2 holds: for every real $X\ge e^{67}$, at least $X/5$ such $N$ are sums of two primes.
-- source:
--   Ramaré 1995, Theorem 2, p. 646; Section 2.3, pp. 653 to 656.

import Mathlib
import Definitions.Def_LL_Decomp1526a_IsGoldbachSum
import Definitions.Def_LL_Decomp1526a_rep
import Definitions.Def_LL_Decomp1526a_evenBlock
import Definitions.Def_LL_Decomp1526a_Theorem2

open Finset Real
open scoped Chebyshev Classical

namespace LL_Decomp1526a
theorem theorem2_of_moments (L U : ℝ) (hL : 0 < L) (hU : 0 < U) (hc : 1 / 5 ≤ L ^ 2 / U)
    (h1 : ∀ X : ℝ, exp 67 ≤ X → L * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N)
    (h2 : ∀ X : ℝ, exp 67 ≤ X → ∑ N ∈ evenBlock X, rep N ^ 2 ≤ U * X ^ 3) : Theorem2 := by sorry
end LL_Decomp1526a
