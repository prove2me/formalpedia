-- Prove2me | Theorems.Thm_MinEarnings_Threshold_theorem_1
-- name    : MinEarnings.Threshold.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:11.422453+00:00
-- url     : https://prove2.me/theorems/ee20e99b-fb57-4cf9-8b42-96669b5d380f
-- title:
--   Theorem 1, p. 11 — exact threshold for marketplace stability
-- statement:
--   Suppose demand and supply satisfy the paper's regularity assumptions. Let $p^*$ be the unique revenue peak, $w^*$ the demand–supply crossing, $R(p)=pD(p)$, $C(z)=zS(z)$, and $H$ the inverse of $C$ on positive costs. For a minimum hourly earnings target $M>0$, the regulated marketplace has a stable policy if and only if
--
--   $$M\le z^*,\qquad z^*=\begin{cases}w^*,&p^*\le w^*,\\H(R(p^*)),&p^*>w^*.\end{cases}$$
--
--   Stability means that some feasible equilibrium policy obeys $w_{t+1}\ge M/u(p_t,z_t)$, has bounded wages, and eventually has nonnegative profit. The threshold distinguishes tight supply, where the crossing wage is decisive, from loose supply, where maximal revenue limits earnings.
--
--   **Formalization Note** Lean indexes the paper's first period by zero, leaving the first wage unconstrained by the rule. Equilibrium requires positive earnings to exclude division by zero in utilization. The paper's differentiability assumption is imposed on positive earnings plus continuity at zero, and unimodality is expressed as strict monotonicity on either side of $p^*$. The threshold uses the paper's two branches exactly.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), p. 11, Theorem 1 and (7); proof Online Appendix pp. 3–5 (PDF 31–33)

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Threshold

theorem theorem_1 (D S H : ℝ → ℝ) (pStar wStar M : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hM : 0 < M) :
    IsStable D S M ↔ M ≤ zStar D H pStar wStar := by sorry

end MinEarnings.Threshold
