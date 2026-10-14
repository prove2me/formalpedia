-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_lemma2_spne_costless
-- name    : ImperfectTargeting.CostlessAds.lemma2_spne_costless
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:45.52998+00:00
-- url     : https://prove2.me/theorems/20cddcda-26d2-4238-a942-88d29b396949
-- title:
--   Lemma 2, pp. 14–15 — the SPNE with c = 0: below α̂₂(A) both target b, one messages expected consumers (F) and one all (H); above, segmentation at prices A and 1
-- statement:
--   Let $0 < A < 1$, $1/2 < \alpha \le 1$, and messaging be costless ($c = 0$). Write $\hat\alpha_2(A) = \bigl(1 + \sqrt{1-4A}\bigr)/2$ and let $F$, $H$ be the cdfs of displays (1) and (2).
--
--   1. If $\hat\alpha_2(A) > 1/2$ and $\alpha < \hat\alpha_2(A)$, there is a subgame perfect Nash equilibrium in which both firms target group $b$, firm 1 messages only the consumers it expects to be in group $b$ and firm 2 messages all consumers, firm 1 prices according to $F$ and firm 2 according to $H$, and the expected profits are
--   $$
--   \pi_1^\star = \alpha(1-\alpha), \qquad \pi_2^\star = 1 - \alpha.
--   $$
--   2. If $\alpha > \max\{1/2, \hat\alpha_2(A)\}$, there is a subgame perfect Nash equilibrium in which the firms segment the market — firm 1 targets group $a$, firm 2 targets group $b$, both message all consumers — with prices $p_1^\star = A$, $p_2^\star = 1$ and profits
--   $$
--   \pi_1^\star = A, \qquad \pi_2^\star = 1.
--   $$
--
--   In each case the equilibrium specifies a pricing equilibrium in every one of the sixteen stage-1 subgames, on and off the path of play. Proposition 2 is read off from the two profit sums.
--
--   **Formalization Note** The statement is in existence form: the paper exhibits these equilibria and says the asymmetric one is the unique equilibrium in pure targeting strategies, but that uniqueness (and uniqueness of equilibrium payoffs in the pricing subgames) is not posed. The paper's "firm $i$ / firm $-i$" are fixed as firm 1 (expected-only firm; group-$a$ firm) and firm 2, as the paper does on p. 14. Targeting is pure; the message scope is binary. For $A > 1/4$, Lean's $\sqrt{\cdot}$ gives $\hat\alpha_2(A) = 1/2$, so part 1 is vacuous and part 2 covers $(1/2, 1]$, as in the paper.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), pp. 14–15, Lemma 2; proof OA pp. 1–3

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem lemma2_spne_costless (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    (1 / 2 < αhat2 A → α < αhat2 A →
      ∃ cont : Action × Action → Measure ℝ × Measure ℝ,
        IsSPNE A α 0 ((.b, .expected), (.b, .all)) cont ∧
        ⇑(ProbabilityTheory.cdf (cont ((.b, .expected), (.b, .all))).1) = Fcdf α ∧
        ⇑(ProbabilityTheory.cdf (cont ((.b, .expected), (.b, .all))).2) = Hcdf α ∧
        V₁ A α 0 cont ((.b, .expected), (.b, .all)) = α * (1 - α) ∧
        V₂ A α 0 cont ((.b, .expected), (.b, .all)) = 1 - α) ∧
    (max (1 / 2) (αhat2 A) < α →
      ∃ cont : Action × Action → Measure ℝ × Measure ℝ,
        IsSPNE A α 0 ((.a, .all), (.b, .all)) cont ∧
        cont ((.a, .all), (.b, .all)) = (Measure.dirac A, Measure.dirac 1) ∧
        V₁ A α 0 cont ((.a, .all), (.b, .all)) = A ∧
        V₂ A α 0 cont ((.a, .all), (.b, .all)) = 1) := by sorry
end ImperfectTargeting.CostlessAds
