-- Prove2me | Theorems.Thm_LL_S106SplitDecomp93_bracket_A7_lower
-- name    : LL_S106SplitDecomp93.bracket_A7_lower
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T03:27:26.489421+00:00
-- url     : https://prove2.me/theorems/792ff986-ef23-5eda-9358-c5c0610e0456
-- title:
--   Lower bracket $-9.260623\le A_7(3/2)$
-- statement:
--   $-9.260623\le A_7(3/2)$. The true value is $-9.2606221815\ldots$, a margin of about $8.2\cdot10^{-7}$; the bound needs $A_0$, $A_2$ and $\gamma_1$ to about seven digits.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 1983, page 47 equations 2.20 to 2.22

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_Lsum
import Definitions.Def_LL_S106SplitDecomp93_cseq
import Definitions.Def_LL_S106SplitDecomp93_gamma1Seq
import Definitions.Def_LL_S106SplitDecomp93_stieltjes1
import Definitions.Def_LL_S106SplitDecomp93_A0
import Definitions.Def_LL_S106SplitDecomp93_A1
import Definitions.Def_LL_S106SplitDecomp93_A2
import Definitions.Def_LL_S106SplitDecomp93_A3
import Definitions.Def_LL_S106SplitDecomp93_A4
import Definitions.Def_LL_S106SplitDecomp93_A7one
import Definitions.Def_LL_S106SplitDecomp93_A7

open Real

namespace LL_S106SplitDecomp93
theorem bracket_A7_lower : -(9260623 / 1000000 : ℝ) ≤ A7 (3 / 2) := by sorry
end LL_S106SplitDecomp93
