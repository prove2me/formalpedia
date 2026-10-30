-- Prove2me | Theorems.Thm_LL_Decomp1543a_wc_lemma2
-- name    : LL_Decomp1543a.wc_lemma2
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:37:44.132593+00:00
-- url     : https://prove2.me/theorems/80406c30-9dd4-4b9f-bf4f-e1c09f1c94ed
-- title:
--   Wang and Chen kernel bound
-- statement:
--   The proposition $\mathrm{WCLemma2}$ holds: for every $\operatorname{Dioph}(\alpha,a,q)$, real $X>0$, natural $Y\ge1$ and integer $Z$, $\sum_{Z<n\le Z+Y}K(X,\alpha n)\le(\lfloor Y/q\rfloor+1)(5X+q\log q)$. The kernel uses distance to the nearest integer, as specified by the lab.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 169, Lemma 6.3, citing Wang and Chen 1994, Lemma 2. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_Dioph
import Definitions.Def_LL_Decomp1543a_WCLemma2

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem wc_lemma2 : WCLemma2 := by sorry
end LL_Decomp1543a
