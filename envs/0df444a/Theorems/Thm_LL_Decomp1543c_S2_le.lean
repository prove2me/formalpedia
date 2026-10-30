-- Prove2me | Theorems.Thm_LL_Decomp1543c_S2_le
-- name    : LL_Decomp1543c.S2_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:32:08.655075+00:00
-- url     : https://prove2.me/theorems/1abebbf7-531e-4418-905b-3ebe104ca85c
-- title:
--   Partial summation bound for $S_2$
-- statement:
--   For real $c\ge0$, $V$, $\alpha$ and natural $N$, $|S_{\Lambda_2(V,\cdot)}(c,N,\alpha)|\le \log N\sum_{t=1}^{\lfloor V\rfloor}K(N/t,\alpha t)$, where $\Lambda_2(V,n)=\sum_{t\mid n,\ t\le V}\mu(t)\log(n/t)$ and $K(X,\theta)=\min(X,1/(2\|\theta\|))$, read as $X$ when $\theta$ is an integer.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.5, first line. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_nint
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_lam2

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem S2_le (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (V α : ℝ) :
    ‖Ssum (lam2 V) c N α‖ ≤
      Real.log N * ∑ t ∈ Icc 1 ⌊V⌋₊, minK ((N : ℝ) / t) (α * t) := by sorry
end LL_Decomp1543c
