-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_lstar_lt_labor
-- name    : LeveragedPayouts.ShockSize.lstar_lt_labor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:15.142091+00:00
-- url     : https://prove2.me/theorems/53989921-f22c-4ca8-8ce1-ae30220123aa
-- title:
--   Appendix B, proof of Proposition 12, p. 58 — date-0 labour exceeds $l^*$ at every rate $r<R$
-- statement:
--   Fix an economy with steady state $(l^*,w^*)$ from (20). Let $0<r<R$ and let $l\in(0,1]$ be the date-0 labour demand at $r$, that is,
--   $$\frac{\pi R f'(l)}{2(2R-r)}=r\,w^*.$$
--   Then
--   $$l>l^*.$$
--
--   Cutting the date-0 rate below $R$ raises investment above its steady-state level. In the proof of Proposition 12 this is the reason the surplus at $r_u=R$, (67), has a larger slope in $\rho$ than the surplus at any interior optimum.
--
--   **Formalization Note** The labour demand is `IsLaborDemand E r l`; for $r<R$ the rate $\bar r(r)=\min\{r,R\}$ equals $r$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 58, Appendix B, proof of Proposition 12, Step 2 ("l_u > l* when r_u < R from (63)")

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem lstar_lt_labor (E : LeveragedPayouts.Unregulated.Economy) (r l : ℝ) (hr0 : 0 < r) (hrR : r < E.R)
    (hl : LeveragedPayouts.Unregulated.IsLaborDemand E r l) : E.lstar < l := by sorry

end LeveragedPayouts.ShockSize
