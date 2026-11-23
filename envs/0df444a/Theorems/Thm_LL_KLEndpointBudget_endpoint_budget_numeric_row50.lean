-- Prove2me | Theorems.Thm_LL_KLEndpointBudget_endpoint_budget_numeric_row50
-- name    : LL_KLEndpointBudget.endpoint_budget_numeric_row50
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T18:05:25.815188+00:00
-- url     : https://prove2.me/theorems/d2d2069a-22f7-4304-b187-4c8f0a0006c3
-- title:
--   Display (2.64) at the endpoint of the Table 2 row $x_0=e^{50}$
-- statement:
--   Let $r$ be the row with log index $50$, $m=20$, $\delta=3889\cdot10^{-12}$, height $8466793105$, $\sigma=93/100$, $a=3543\cdot10^{-4}$ and $\Delta=753575355$; put $u=\delta/m$, $x_0=e^{50}$, $X=x_0/(e^{u}(1+\delta))$, $w_m(t)=(4t(1-t))^m$ and $\nu=\int_0^{a'}w_m+\int_{1-a'}^1 w_m$ with $a'=a+10^{-4}$. Then $2.05022\cdot10^{-3}\sqrt X+T(\delta,u,X)\,\nu\big/\!\int_0^1 w_m+u/(2X)<(e^{u}-1)X\bigl(1+\delta/2-(0.35074+0.02260)\bigr)$, where $T(\delta,u,X)=2(1+\delta)(e^u-1)\frac{\log(e^uX(1+\delta))}{\log(X(e^u-1))}X$.
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
theorem endpoint_budget_numeric_row50 (r : PrintedRow) (hr : r = ⟨50, 20, 3889, 8466793105, 93, 3543, 753575355⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by sorry
end LL_KLEndpointBudget
