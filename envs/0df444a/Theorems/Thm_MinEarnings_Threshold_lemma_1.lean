-- Prove2me | Theorems.Thm_MinEarnings_Threshold_lemma_1
-- name    : MinEarnings.Threshold.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:15.16158+00:00
-- url     : https://prove2.me/theorems/537e259a-ad4d-493c-b962-b9d9692026c5
-- title:
--   Lemma 1, p. 9 — inverse labor cost and declining earnings per expenditure
-- statement:
--   Let $D$ and $S$ satisfy the paper's standing regularity assumptions, including the revenue peak and demand–supply crossing, and set $C(z)=zS(z)$. There is an inverse $H$ of $C$ on positive expenditures. Every such inverse is strictly increasing and differentiable on $(0,\infty)$, while $H(x)/x$ is strictly decreasing there:
--
--   $$x>0\Longrightarrow C(H(x))=x,\qquad x_1<x_2\Longrightarrow \frac{H(x_1)}{x_1}>\frac{H(x_2)}{x_2}.$$
--
--   The result makes the inverse cost used throughout the stability analysis well defined and orders the labor supplied per unit of expenditure.
--
--   **Formalization Note** The existence assertion makes explicit the appendix's claim that the domain of $H$ includes $(0,\infty)$. The inverse is unconstrained outside that domain. Supply differentiability is required only at positive earnings, plus continuity on $[0,\infty)$; both monotonicity conclusions use the strict form implied by strict supply growth.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), p. 9, Lemma 1; proof Online Appendix p. 1 (PDF 29)

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Threshold

theorem lemma_1 (D S : ℝ → ℝ) (pStar wStar : ℝ)
    (hA : Assumptions D S pStar wStar) :
    (∃ H : ℝ → ℝ, IsCostInverse S H) ∧
      ∀ H : ℝ → ℝ, IsCostInverse S H →
        StrictMonoOn H (Set.Ioi 0) ∧
        (∀ x, 0 < x → DifferentiableAt ℝ H x) ∧
        StrictAntiOn (fun x => H x / x) (Set.Ioi 0) := by sorry

end MinEarnings.Threshold
