-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_segmentation_equilibrium
-- name    : ImperfectTargeting.CostlessAds.segmentation_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:40.016086+00:00
-- url     : https://prove2.me/theorems/79e5dee5-7b8e-4ebd-9b75-73dc9a0dd776
-- title:
--   §4.1 p. 9, §4.2 p. 13 — market segmentation: firm 1 on group a, firm 2 on group b, prices A and 1 are a Nash equilibrium, profits r₁A and r₂
-- statement:
--   Consider a pricing subgame in which firm 1 targets the low-valuation group $a$ and firm 2 targets the high-valuation group $b$, each with any message scope $m_1, m_2 \in \{\text{expected}, \text{all}\}$. There are no shoppers, and firm $i$'s loyal mass is its reach $r(m_i)$, where $r(\text{expected}) = \alpha$ and $r(\text{all}) = 1$.
--
--   Let $0 < A < 1$ and $1/2 < \alpha \le 1$. Then firm 1 charging $A$ and firm 2 charging $1$ (point masses $\delta_A$, $\delta_1$) is a Nash equilibrium of the pricing subgame, with expected profits
--   $$
--   U_1 = r(m_1)\, A, \qquad U_2 = r(m_2).
--   $$
--
--   In particular, with messages only to the expected groups the profits are $\alpha A$ and $\alpha$ (p. 9, before costs), and with messages to all consumers they are $A$ and $1$, the profits $\pi_1 = A$, $\pi_2 = 1$ of the costless case (p. 13: "In the Nash equilibrium of the pricing game, firms set prices of $p_i = A$ and $p_{-i} = 1$. … Then, the corresponding profits are $\pi_1 = A$ and $\pi_2 = 1$ (as advertising costs are zero).").
--
--   **Formalization Note** Firm 1 is the group-$a$ firm, the paper's own convention ("suppose that firm 1 targets consumers of group a"). The profits are pricing-stage profits, before messaging costs.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 9, §4.1, case (i); p. 13, §4.2, first paragraph

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem segmentation_equilibrium (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    ∀ s₁ s₂ : Scope,
      IsPricingNE A α ((.a, s₁), (.b, s₂)) (Measure.dirac A) (Measure.dirac 1) ∧
      U₁ A α ((.a, s₁), (.b, s₂)) (Measure.dirac A) (Measure.dirac 1) = reach α s₁ * A ∧
      U₂ A α ((.a, s₁), (.b, s₂)) (Measure.dirac A) (Measure.dirac 1) = reach α s₂ := by sorry
end ImperfectTargeting.CostlessAds
