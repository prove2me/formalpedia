-- Prove2me | Theorems.Thm_LL_Decomp119LeavesIIS124CaseBRatio_caseB_ratio
-- name    : LL_Decomp119LeavesIIS124CaseBRatio.caseB_ratio
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T16:28:25.561804+00:00
-- url     : https://prove2.me/theorems/958b272a-99ca-46d1-9e59-4902fe12a26e
-- title:
--   Case b display bound for all $x\ge 2.16\cdot 10^{20}$
-- statement:
--   For every real $x\ge 2.16\cdot 10^{20}$, the case b display satisfies $D(x)\le 0.24956\,x^{5/6}\log^{3/2}x$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, page 72, case b

import Mathlib
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_U
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_V
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_frakF
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_caseBDisplay

namespace LL_Decomp119LeavesIIS124CaseBRatio
theorem caseB_ratio (x : ℝ) (hx : 2.16e20 ≤ x) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by sorry
end LL_Decomp119LeavesIIS124CaseBRatio
