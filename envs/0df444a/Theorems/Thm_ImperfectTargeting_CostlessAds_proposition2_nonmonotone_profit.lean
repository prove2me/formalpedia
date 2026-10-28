-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_proposition2_nonmonotone_profit
-- name    : ImperfectTargeting.CostlessAds.proposition2_nonmonotone_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:54.296702+00:00
-- url     : https://prove2.me/theorems/c1afc847-3834-4672-9fa8-2fb81f79912b
-- title:
--   Proposition 2, p. 15 — for A < 1/4 and c = 0, SPNE industry profit is 1 − α² below α̂₂(A) (decreasing), jumps up, and is 1 + A above; α̂₂(A) < α̂₁(A)
-- statement:
--   Consider the targeting-and-pricing game with costless advertising ($c = 0$): two firms each choose a consumer group to target (low valuation $A$ or high valuation $1$) and whether to message only the consumers their signal places in that group or all consumers, then compete in prices; signals are correct with probability $\alpha \in (1/2, 1]$. Let $\hat\alpha_1(A) = 1 - A$ and $\hat\alpha_2(A) = \bigl(1 + \sqrt{1-4A}\bigr)/2$.
--
--   **Proposition 2.** If $0 < A < 1/4$, the sum of the firms' expected equilibrium profits is non-monotonic in $\alpha$:
--
--   1. $\hat\alpha_2(A) > 1/2$ and $\hat\alpha_2(A) < \hat\alpha_1(A)$;
--   2. for every $\alpha \in (1/2, \hat\alpha_2(A))$ there is a subgame perfect Nash equilibrium whose sum of expected profits is
--   $$
--   \sum_i E[\pi_i^\star(\alpha)] = 1 - \alpha^2,
--   $$
--   and $\alpha \mapsto 1 - \alpha^2$ is strictly decreasing on $[1/2, \hat\alpha_2(A))$;
--   3. for every $\alpha \in (\hat\alpha_2(A), 1]$ there is a subgame perfect Nash equilibrium whose sum of expected profits is $1 + A$, a constant;
--   4. the profit sum jumps upwards at $\hat\alpha_2(A)$: $1 - \hat\alpha_2(A)^2 < 1 + A$.
--
--   Better targeting first lowers industry profit, because more consumers receive both firms' messages and price competition intensifies, until the firms switch to segmenting the market, after which industry profit is flat. The result shows that the non-monotonicity of the paper's high-cost case survives when advertising is free.
--
--   **Formalization Note** The statement is in existence form: the paper's "sum of expected profits" is the total in the equilibrium of Lemma 2; uniqueness of equilibrium payoffs is not claimed or posed. An SPNE consists of a pure targeting profile and a pricing equilibrium (in mixed prices concentrated on $[0,1]$) in every one of the sixteen stage-1 subgames; the stage-1 values are the expected profits of those pricing equilibria. The message scope is binary (expected group or all consumers). "Decreases" and "jumps upwards" are stated through the profit formula of each regime.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 15, Proposition 2 and the aggregate-profit display before it; Lemma 2, pp. 14–15; footnote 36

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem proposition2_nonmonotone_profit (A : ℝ) (hA0 : 0 < A) (hA : A < 1 / 4) :
    1 / 2 < αhat2 A ∧
    αhat2 A < αhat1 A ∧
    (∀ α : ℝ, 1 / 2 < α → α < αhat2 A →
      ∃ (play : Action × Action) (cont : Action × Action → Measure ℝ × Measure ℝ),
        IsSPNE A α 0 play cont ∧ totalProfit A α 0 play cont = 1 - α ^ 2) ∧
    (∀ α : ℝ, αhat2 A < α → α ≤ 1 →
      ∃ (play : Action × Action) (cont : Action × Action → Measure ℝ × Measure ℝ),
        IsSPNE A α 0 play cont ∧ totalProfit A α 0 play cont = 1 + A) ∧
    StrictAntiOn (fun α : ℝ => 1 - α ^ 2) (Set.Ico (1 / 2) (αhat2 A)) ∧
    1 - αhat2 A ^ 2 < 1 + A := by sorry
end ImperfectTargeting.CostlessAds
