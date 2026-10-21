-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_effort_labor_monotone
-- name    : LeveragedPayouts.Unregulated.effort_labor_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:22.473301+00:00
-- url     : https://prove2.me/theorems/0bf47058-f54e-4ae0-821d-6287e16b7da3
-- title:
--   Appendix B, proof of Proposition 11, p. 56 — effort e(r) increases and labour demand l(r) decreases in the date-0 rate r
-- statement:
--   In the economy of the mission, let $e(r)=\pi R/(2R-\min\{r;R\})$ be the effort and $l(r)$ the labour demand at the date-0 rate $r>0$. Then:
--   1. $e$ is strictly increasing on $(0,R]$;
--   2. $e(r)=\pi$ for every $r\ge R$;
--   3. labour demand is strictly decreasing in the rate: if $0<r<r'$, $l$ is a labour demand at $r$ and $l'$ is a labour demand at $r'$, then
--   $$l'<l .$$
--
--   The third item implies in particular that the labour demand at each rate is unique. These monotonicity properties drive the trade-off of the planner in Proposition 11: lowering the rate raises date-0 employment but lowers effort.
--
--   **Formalization Note** The paper also says that $e(r)$ and $l(r)$ are "obviously differentiable"; differentiability is not part of this statement. Item 3 covers rates on both sides of $R$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 56, Appendix B, proof of Proposition 11, after (59)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.Unregulated
theorem effort_labor_monotone (E : Economy) :
    StrictMonoOn (effort E) (Set.Ioc 0 E.R) ∧
    (∀ r, E.R ≤ r → effort E r = E.π) ∧
    ∀ r r' l l', 0 < r → r < r' → IsLaborDemand E r l → IsLaborDemand E r' l' → l' < l := by sorry
end LeveragedPayouts.Unregulated
