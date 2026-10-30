-- Prove2me | Theorems.Thm_LL_Decomp1543a_inner_l_sum
-- name    : LL_Decomp1543a.inner_l_sum
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:40:41.00899+00:00
-- url     : https://prove2.me/theorems/52126ac4-d65d-4619-b4a8-aae74cd839bc
-- title:
--   Kernel sum conditional on the Wang and Chen input
-- statement:
--   Assume $\mathrm{WCLemma2}$ and $\operatorname{Dioph}(\alpha,a,q)$. For every natural $N,m$, real $U\ge0$, real $Y$ and real $X>0$, $\sum_{l\in L(N,U,Y)}K(X,\alpha(m-l))\le\left(\left\lfloor\frac{\max(\lfloor Y\rfloor_+-\lfloor U\rfloor_+,0)}q\right\rfloor+1\right)(5X+q\log q)$, where the subtraction and division in the bracket are natural-number operations.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 171, equation 6.12. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_Dioph
import Definitions.Def_LL_Decomp1543a_lRange
import Definitions.Def_LL_Decomp1543a_WCLemma2

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem inner_l_sum (hwc : WCLemma2) (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (N : ℕ)
    (U Y X : ℝ) (hU : 0 ≤ U) (hX : 0 < X) (m : ℕ) :
    ∑ l ∈ lRange N U Y, minK X (α * ((m : ℝ) - l)) ≤
      ((((⌊Y⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q) := by sorry
end LL_Decomp1543a
