-- Prove2me | Theorems.Thm_LL_S106SplitDecomp93_bracket_A9_upper
-- name    : LL_S106SplitDecomp93.bracket_A9_upper
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T03:23:21.220612+00:00
-- url     : https://prove2.me/theorems/e9b2ecf3-7bf2-433d-8512-47dcf9da4c47
-- title:
--   Upper bracket $A_9(3/2)\le 29.50889$
-- statement:
--   $A_9(3/2)=4A_3\sqrt{3/2}\le 29.50889$. The true value is $29.5088867446\ldots$, a margin of about $3.3\cdot10^{-6}$.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 1983, page 47 equations 2.20 to 2.22

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A0
import Definitions.Def_LL_S106SplitDecomp93_A1
import Definitions.Def_LL_S106SplitDecomp93_A3
import Definitions.Def_LL_S106SplitDecomp93_A9

open Real

namespace LL_S106SplitDecomp93
theorem bracket_A9_upper : A9 (3 / 2) ≤ (2950889 / 100000 : ℝ) := by sorry
end LL_S106SplitDecomp93
