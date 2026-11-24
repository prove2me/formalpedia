-- Prove2me | Theorems.Thm_LL_S106SplitDecomp93_bracket_A6_lower
-- name    : LL_S106SplitDecomp93.bracket_A6_lower
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T18:18:56.042805+00:00
-- url     : https://prove2.me/theorems/8561a5f7-29bd-412a-8fbe-70ff6edb0ccd
-- title:
--   Lower bracket $8.463433\le A_6(3/2)$
-- statement:
--   $8.463433\le A_6(3/2)=2A_3-4\log2-2\log\tfrac32$. The true value is $8.4634336285\ldots$, a margin of about $6.3\cdot10^{-7}$.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 1983, page 47 equations 2.20 to 2.22

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A0
import Definitions.Def_LL_S106SplitDecomp93_A1
import Definitions.Def_LL_S106SplitDecomp93_A3
import Definitions.Def_LL_S106SplitDecomp93_A6

open Real

namespace LL_S106SplitDecomp93
theorem bracket_A6_lower : (8463433 / 1000000 : ℝ) ≤ A6 (3 / 2) := by sorry
end LL_S106SplitDecomp93
