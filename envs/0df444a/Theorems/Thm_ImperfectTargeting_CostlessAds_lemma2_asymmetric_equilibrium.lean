-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_lemma2_asymmetric_equilibrium
-- name    : ImperfectTargeting.CostlessAds.lemma2_asymmetric_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:40.225104+00:00
-- url     : https://prove2.me/theorems/893baade-6838-4a76-8d99-4c954169605f
-- title:
--   Lemma 2 part 1, display (2), pp. 14–15 — expected-only vs message-all on group b: (F, H) is a pricing equilibrium, profits α(1−α) and 1−α
-- statement:
--   Consider the pricing subgame in which both firms target group $b$, firm 1 messages only the consumers it expects to be in group $b$ and firm 2 messages all consumers. Then a mass $\alpha$ of group-$b$ consumers are shoppers, firm 1 has no loyal consumers and firm 2 has a mass $1-\alpha$ of them.
--
--   Let $1/2 < \alpha < 1$, let $F$ be the cdf of display (1) and $H$ the cdf of display (2),
--   $$
--   H(p) = \begin{cases} \dfrac{p - (1-\alpha)}{p}, & p \in [1-\alpha, 1),\\[4pt] 1, & p = 1, \end{cases}
--   $$
--   with $H = 0$ below $1-\alpha$ and $H = 1$ above $1$, so $H$ puts a mass point of $1-\alpha$ at $p = 1$. Then:
--
--   1. there are probability measures on $\mathbb R$ with cdf $F$ and with cdf $H$;
--   2. for all probability measures $\mu$ with cdf $F$ and $\nu$ with cdf $H$, the profile in which firm 1 prices by $\mu$ and firm 2 by $\nu$ is a Nash equilibrium of the pricing subgame, with expected profits
--   $$
--   U_1 = \alpha(1-\alpha), \qquad U_2 = 1 - \alpha.
--   $$
--
--   This is the pricing equilibrium on the path of Lemma 2's first regime, in which the asymmetry of message scopes softens price competition.
--
--   **Formalization Note** The paper's "firm $i$" (messaging expected consumers) is firm 1 and "firm $-i$" (messaging all consumers) is firm 2; the game is symmetric, so this loses nothing. The case $\alpha = 1$ is excluded because $F$ and $H$ degenerate there; Lemma 2's first regime has $\alpha < \hat\alpha_2(A) < 1$. $A$ plays no role and is kept for the uniform signature.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), pp. 14–15, Lemma 2 part 1, display (2); derived OA pp. 1–2

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem lemma2_asymmetric_equilibrium (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α < 1) :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ⇑(ProbabilityTheory.cdf μ) = Fcdf α) ∧
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ⇑(ProbabilityTheory.cdf ν) = Hcdf α) ∧
    ∀ μ ν : Measure ℝ, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      ⇑(ProbabilityTheory.cdf μ) = Fcdf α → ⇑(ProbabilityTheory.cdf ν) = Hcdf α →
      IsPricingNE A α ((.b, .expected), (.b, .all)) μ ν ∧
      U₁ A α ((.b, .expected), (.b, .all)) μ ν = α * (1 - α) ∧
      U₂ A α ((.b, .expected), (.b, .all)) μ ν = 1 - α := by sorry
end ImperfectTargeting.CostlessAds
