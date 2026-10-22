-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_threshold_alpha_hat2_iff
-- name    : ImperfectTargeting.CostlessAds.threshold_alpha_hat2_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:40.13998+00:00
-- url     : https://prove2.me/theorems/e3231411-2ddb-4ff9-92a6-18bf92ef8bf5
-- title:
--   p. 14 — α(1 − α) ≥ A if and only if α ≤ α̂₂(A) = (1 + √(1 − 4A))/2, for 0 < A ≤ 1/4 and α ∈ (1/2, 1]
-- statement:
--   Let $0 < A \le 1/4$ and $1/2 < \alpha \le 1$, and let $\hat\alpha_2(A) = \bigl(1 + \sqrt{1-4A}\bigr)/2$. Then
--   $$
--   \alpha(1-\alpha) \ge A \iff \alpha \le \hat\alpha_2(A).
--   $$
--
--   The left-hand side compares the profit $\alpha(1-\alpha)$ of the firm that messages only expected group-$b$ consumers against a rival that messages all of group $b$ with the profit $A$ it would earn by targeting group $a$ instead. The equivalence turns this comparison into the threshold $\hat\alpha_2(A)$ that separates the two regimes of Lemma 2.
--
--   **Formalization Note** The hypothesis $A \le 1/4$ keeps $1 - 4A \ge 0$, so that $\hat\alpha_2(A)$ is the real root the paper writes; the display is used in the paper only in that range.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 14, display before Lemma 2

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem threshold_alpha_hat2_iff (A α : ℝ) (hA0 : 0 < A) (hA : A ≤ 1 / 4)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    A ≤ α * (1 - α) ↔ α ≤ αhat2 A := by sorry
end ImperfectTargeting.CostlessAds
