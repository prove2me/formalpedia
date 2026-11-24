-- Prove2me | Theorems.Thm_LL_Decomp119LeavesIIS124CaseBRatio_caseB_ratio_high
-- name    : LL_Decomp119LeavesIIS124CaseBRatio.caseB_ratio_high
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T16:14:37.043004+00:00
-- url     : https://prove2.me/theorems/84c8c0c3-92cf-452b-b8ae-36813614031c
-- title:
--   Case b display bound for $x\ge 10^{25}$
-- statement:
--   For every real $x\ge 10^{25}$, $D(x)\le 0.24956\,x^{5/6}\log^{3/2}x$. Numerically the ratio is at most about $0.24556$ on this range and tends to $0$ as $x\to\infty$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, page 72, case b

import Mathlib
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_U
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_V
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_frakF
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_caseBDisplay

namespace LL_Decomp119LeavesIIS124CaseBRatio
theorem caseB_ratio_high (x : ℝ) (hx1 : 1e25 ≤ x) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by sorry
end LL_Decomp119LeavesIIS124CaseBRatio
