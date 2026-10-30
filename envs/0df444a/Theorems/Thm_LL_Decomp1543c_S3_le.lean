-- Prove2me | Theorems.Thm_LL_Decomp1543c_S3_le
-- name    : LL_Decomp1543c.S3_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:32:47.437924+00:00
-- url     : https://prove2.me/theorems/9b0db842-cf74-4f72-bbbb-fec6789a7830
-- title:
--   Divisor bound for $S_3$
-- statement:
--   For real $c\ge0$, $U,V\ge1$, $\alpha$ and natural $N$, $|S_{\Lambda_3(U,V,\cdot)}(c,N,\alpha)|\le \log(UV)\sum_{k=1}^{\lfloor UV\rfloor}K(N/k,\alpha k)$, where $\Lambda_3(U,V,n)=-\sum_{rt\mid n,\ r\le U,\ t\le V}\Lambda(r)\mu(t)$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, proof of Lemma 6.6, first line. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_nint
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_lam3

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem S3_le (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (U V α : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ‖Ssum (lam3 U V) c N α‖ ≤
      Real.log (U * V) * ∑ k ∈ Icc 1 ⌊U * V⌋₊, minK ((N : ℝ) / k) (α * k) := by sorry
end LL_Decomp1543c
