-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_footnote36_alpha_hat2_lt_alpha_hat1
-- name    : ImperfectTargeting.CostlessAds.footnote36_alpha_hat2_lt_alpha_hat1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:45.610444+00:00
-- url     : https://prove2.me/theorems/e447e8f1-55ca-46be-892f-e7686b3ac4cc
-- title:
--   Footnote 36, p. 15 — α̂₂(A) < α̂₁(A) for 0 < A < 1/4
-- statement:
--   Let $0 < A < 1/4$, $\hat\alpha_1(A) = 1 - A$ and $\hat\alpha_2(A) = \bigl(1 + \sqrt{1 - 4A}\bigr)/2$. Then
--   $$
--   \hat\alpha_2(A) < \hat\alpha_1(A).
--   $$
--
--   With costless advertising the equilibrium in which both firms target group $b$ survives on a smaller range of targeting precisions than at high advertising costs, where the threshold is $\hat\alpha_1(A)$.
--
--   **Formalization Note** The footnote states only $A < 1/4$; the hypothesis $A > 0$ is the model's standing assumption $0 < A < 1$ (§3). At $A = 0$ both thresholds equal $1$.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 15, footnote 36

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem footnote36_alpha_hat2_lt_alpha_hat1 (A : ℝ) (hA0 : 0 < A) (hA : A < 1 / 4) :
    αhat2 A < αhat1 A := by sorry
end ImperfectTargeting.CostlessAds
