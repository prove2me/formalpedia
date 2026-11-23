-- Prove2me | Theorems.Thm_LL_KLEndpointBudget_endpoint_budget_numeric_row57
-- name    : LL_KLEndpointBudget.endpoint_budget_numeric_row57
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T18:12:43.781654+00:00
-- url     : https://prove2.me/theorems/a8f2a58f-2829-46e8-a82b-18d91893bade
-- title:
--   Display (2.64) at the endpoint of the Table 2 row $x_0=e^{57}$
-- statement:
--   Let $r$ be the row with log index $57$, $m=59$, $\delta=4506\cdot10^{-12}$, height $20219045843$, $\sigma=93/100$, $a=4496\cdot10^{-4}$ and $\Delta=1886389443$; put $u=\delta/m$, $x_0=e^{57}$, $X=x_0/(e^{u}(1+\delta))$, $w_m(t)=(4t(1-t))^m$ and $\nu=\int_0^{a'}w_m+\int_{1-a'}^1 w_m$ with $a'=a+10^{-4}$. Then $2.05022\cdot10^{-3}\sqrt X+T(\delta,u,X)\,\nu\big/\!\int_0^1 w_m+u/(2X)<(e^{u}-1)X\bigl(1+\delta/2-(0.01602+0.05926)\bigr)$, where $T(\delta,u,X)=2(1+\delta)(e^u-1)\frac{\log(e^uX(1+\delta))}{\log(X(e^u-1))}X$.
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
theorem endpoint_budget_numeric_row57 (r : PrintedRow) (hr : r = ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by sorry
end LL_KLEndpointBudget
