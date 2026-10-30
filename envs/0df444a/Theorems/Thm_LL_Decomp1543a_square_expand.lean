-- Prove2me | Theorems.Thm_LL_Decomp1543a_square_expand
-- name    : LL_Decomp1543a.square_expand
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:39:54.261097+00:00
-- url     : https://prove2.me/theorems/0cfd206f-f322-4772-9d00-a16daf4efc96
-- title:
--   Second-moment bound conditional on geometric sums
-- statement:
--   For real $c,\alpha$, natural $N$, $U\ge0$ and $M\ge1$, assume $\left|\sum_{A<t\le B}e(\theta t)\right|\le K(M+1/2,\theta)$ for every real $\theta$ and integers $A,B$ with $\lfloor M\rfloor\le A$ and $B\le\lfloor2M\rfloor$. Conditional on that hypothesis, $\sum_{t\in T(N,M)}|I(c,N,U,\alpha,t)|^2\le\sum_{m\in L(N,U,N/M)}a_m(U)^2\sum_{l\in L(N,U,N/M)}K(M+1/2,\alpha(m-l))$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 171, first display following equation 6.11. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_tBlock
import Definitions.Def_LL_Decomp1543a_mRange
import Definitions.Def_LL_Decomp1543a_inner
import Definitions.Def_LL_Decomp1543a_lRange

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem square_expand (c : ℝ) (N : ℕ) (U M α : ℝ) (hU : 0 ≤ U) (hM : 1 ≤ M)
    (hgeom : ∀ θ : ℝ, ∀ A B : ℤ, ⌊M⌋ ≤ A → B ≤ ⌊2 * M⌋ →
      ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ) :
    ∑ t ∈ tBlock N M, ‖inner c N U α t‖ ^ 2 ≤
      ∑ m ∈ lRange N U (N / M), am U m ^ 2 *
        ∑ l ∈ lRange N U (N / M), minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by sorry
end LL_Decomp1543a
