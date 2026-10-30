-- Prove2me | Theorems.Thm_LL_Decomp1543c_wc_lemma3
-- name    : LL_Decomp1543c.wc_lemma3
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:31:25.177506+00:00
-- url     : https://prove2.me/theorems/4d14178b-f61f-44c7-984d-efc77d7e0c38
-- title:
--   Wang and Chen kernel sum bound (cited)
-- statement:
--   CITED input, stated as an open item. The proposition $\mathrm{WCLemma3}$ holds: whenever $\operatorname{Dioph}(\alpha,a,q)$, $q\ge15$, $X\ge1$ and $Y>0$, one has $\sum_{n=1}^{\lfloor X\rfloor}K(Y/n,\alpha n)\le 5q+1.5\,q\log q+X\log q+5\,(Y/q)\log X$, where $K(Y,\theta)=\min(Y,1/(2\|\theta\|))$ with $\|\theta\|$ the distance to the nearest integer.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 169, Lemma 6.4, citing T. Z. Wang and J. R. Chen, Acta Math. Sinica 37, 1994, Lemma 3. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_nint
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_Dioph
import Definitions.Def_LL_Decomp1543c_WCLemma3

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem wc_lemma3 : WCLemma3 := by sorry
end LL_Decomp1543c
