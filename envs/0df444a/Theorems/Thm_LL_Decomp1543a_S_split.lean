-- Prove2me | Theorems.Thm_LL_Decomp1543a_S_split
-- name    : LL_Decomp1543a.S_split
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:52:33.392216+00:00
-- url     : https://prove2.me/theorems/94ec3356-e47a-4bd0-88e6-40999cc2a2da
-- title:
--   Assembly of the four Vaughan exponential sums
-- statement:
--   For every real $c,U,V,\alpha$ and natural $N$ with $V\ge1$, $S_\Lambda(c,N,\alpha)=S_{\Lambda_1(U,\cdot)}(c,N,\alpha)+S_{\Lambda_2(V,\cdot)}(c,N,\alpha)+S_{\Lambda_3(U,V,\cdot)}(c,N,\alpha)+S_{\Lambda_4(U,V,\cdot)}(c,N,\alpha)$. All sums use the strict lower cutoff $cN<n$ and $1\le n\le N$; this is the lab assembly conditional on the coefficient identity.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 168, equation 6.7, with definitions in equation 6.8 on p. 169. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_rangeN
import Definitions.Def_LL_Decomp1543a_Ssum
import Definitions.Def_LL_Decomp1543a_lam1
import Definitions.Def_LL_Decomp1543a_lam2
import Definitions.Def_LL_Decomp1543a_lam3
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_lam4

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem S_split (c : ℝ) (N : ℕ) (U V α : ℝ) (hV : 1 ≤ V) :
    Ssum (fun n => (vonMangoldt n : ℝ)) c N α =
      Ssum (lam1 U) c N α + Ssum (lam2 V) c N α + Ssum (lam3 U V) c N α +
        Ssum (lam4 U V) c N α := by sorry
end LL_Decomp1543a
