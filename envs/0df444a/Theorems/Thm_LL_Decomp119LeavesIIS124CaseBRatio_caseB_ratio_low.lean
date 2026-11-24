-- Prove2me | Theorems.Thm_LL_Decomp119LeavesIIS124CaseBRatio_caseB_ratio_low
-- name    : LL_Decomp119LeavesIIS124CaseBRatio.caseB_ratio_low
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T16:00:43.958503+00:00
-- url     : https://prove2.me/theorems/5d3b70f1-db27-4a93-a8aa-cf18d2a9fc29
-- title:
--   Case b display bound on $2.16\cdot 10^{20}\le x\le 10^{25}$
-- statement:
--   For every real $x$ with $2.16\cdot 10^{20}\le x\le 10^{25}$, $D(x)\le 0.24956\,x^{5/6}\log^{3/2}x$. The numerical margin is about $8.7\cdot 10^{-6}$ in the ratio, attained at the left endpoint.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, page 72, case b

import Mathlib
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_U
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_V
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_frakF
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_caseBDisplay

namespace LL_Decomp119LeavesIIS124CaseBRatio
theorem caseB_ratio_low (x : ℝ) (hx : 2.16e20 ≤ x) (hx1 : x ≤ 1e25) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by sorry
end LL_Decomp119LeavesIIS124CaseBRatio
