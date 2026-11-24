-- Prove2me | Theorems.Thm_LL_KLEndpointBudget_endpoint_budget_numeric_row55
-- name    : LL_KLEndpointBudget.endpoint_budget_numeric_row55
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T18:11:14.831581+00:00
-- url     : https://prove2.me/theorems/a5a22a7c-d6ad-496a-aa26-671f7d9aa1c2
-- title:
--   Display (2.64) at the endpoint of the Table 2 row $x_0=e^{55}$
-- statement:
--   Let $r$ be the row with log index $55$, $m=56$, $\delta=4386\cdot10^{-12}$, height $19757119193$, $\sigma=93/100$, $a=4445\cdot10^{-4}$ and $\Delta=1770251249$; put $u=\delta/m$, $x_0=e^{55}$, $X=x_0/(e^{u}(1+\delta))$, $w_m(t)=(4t(1-t))^m$ and $\nu=\int_0^{a'}w_m+\int_{1-a'}^1 w_m$ with $a'=a+10^{-4}$. Then $2.05022\cdot10^{-3}\sqrt X+T(\delta,u,X)\,\nu\big/\!\int_0^1 w_m+u/(2X)<(e^{u}-1)X\bigl(1+\delta/2-(0.04355+0.05902)\bigr)$, where $T(\delta,u,X)=2(1+\delta)(e^u-1)\frac{\log(e^uX(1+\delta))}{\log(X(e^u-1))}X$.
-- source:
--   Kadiri and Lumley 2014, Short effective intervals containing primes, Integers 14 A61, arXiv:1407.7902v1, page 9 Theorem 2.7 display (2.64) and page 13 Table 2.

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow
import Definitions.Def_LL_KLEndpointBudget_evenBase
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_threshold
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_deltaQ
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_uQ
import Definitions.Def_LL_KLEndpointBudget_rowEndpointX
import Definitions.Def_LL_KLEndpointBudget_lowZeroBudget
import Definitions.Def_LL_KLEndpointBudget_highZeroBudget
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_aQ
import Definitions.Def_LL_KLEndpointBudget_weight
import Definitions.Def_LL_KLEndpointBudget_tailMass
import Definitions.Def_LL_KLEndpointBudget_tailCoefficient

open Real Set MeasureTheory

namespace LL_KLEndpointBudget
theorem endpoint_budget_numeric_row55 (r : PrintedRow) (hr : r = ⟨55, 56, 4386, 19757119193, 93, 4445, 1770251249⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by sorry
end LL_KLEndpointBudget
