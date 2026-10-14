-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_bertrand_zero_profit
-- name    : ImperfectTargeting.CostlessAds.bertrand_zero_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:50.514669+00:00
-- url     : https://prove2.me/theorems/06b90d81-7cf0-44c3-b138-148516ba91d6
-- title:
--   §4.2, p. 13 — both firms target group b and message all consumers: Bertrand competition, pricing at 0, zero profits
-- statement:
--   Consider the pricing subgame in which both firms target group $b$ and message all consumers. Then every group-$b$ consumer is a shopper (shopper mass $1$) and neither firm has loyal consumers.
--
--   Let $1/2 < \alpha \le 1$. Both firms charging the price $0$ (each playing the point mass $\delta_0$) is a Nash equilibrium of this pricing subgame, and both expected profits are zero:
--   $$
--   U_1(\delta_0, \delta_0) = U_2(\delta_0, \delta_0) = 0.
--   $$
--
--   This is the paper's observation that messaging all consumers on both sides "leads to Bertrand competition and, therefore, zero profits"; it rules out the symmetric message-all configuration as an equilibrium with costless advertising.
--
--   **Formalization Note** The page states only "zero profits". The pure equilibrium at price $0$ is the standard reading of Bertrand competition with zero marginal cost, and is the reading posed here.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 13, §4.2, second paragraph

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem bertrand_zero_profit (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    IsPricingNE A α ((.b, .all), (.b, .all)) (Measure.dirac 0) (Measure.dirac 0) ∧
    U₁ A α ((.b, .all), (.b, .all)) (Measure.dirac 0) (Measure.dirac 0) = 0 ∧
    U₂ A α ((.b, .all), (.b, .all)) (Measure.dirac 0) (Measure.dirac 0) = 0 := by sorry
end ImperfectTargeting.CostlessAds
