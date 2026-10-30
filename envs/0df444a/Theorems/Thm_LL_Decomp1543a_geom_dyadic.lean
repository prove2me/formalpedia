-- Prove2me | Theorems.Thm_LL_Decomp1543a_geom_dyadic
-- name    : LL_Decomp1543a.geom_dyadic
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:39:10.642984+00:00
-- url     : https://prove2.me/theorems/b99c7f07-1186-4bf7-8cc8-76bc32723770
-- title:
--   Geometric sum on a dyadic integer interval
-- statement:
--   For all real $\theta$, $M\ge0$ and integers $A,B$ with $\lfloor M\rfloor\le A$ and $B\le\lfloor2M\rfloor$, $\left|\sum_{A<t\le B}e(\theta t)\right|\le K(M+1/2,\theta)$. The statement imposes no further restriction on $M$ or on the order of $A,B$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 171, geometric-sum input to the first display. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem geom_dyadic (θ M : ℝ) (hM : 0 ≤ M) (A B : ℤ) (hA : ⌊M⌋ ≤ A) (hB : B ≤ ⌊2 * M⌋) :
    ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ := by sorry
end LL_Decomp1543a
