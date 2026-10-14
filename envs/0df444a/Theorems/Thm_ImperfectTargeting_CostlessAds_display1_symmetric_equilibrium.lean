-- Prove2me | Theorems.Thm_ImperfectTargeting_CostlessAds_display1_symmetric_equilibrium
-- name    : ImperfectTargeting.CostlessAds.display1_symmetric_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:42.392579+00:00
-- url     : https://prove2.me/theorems/492f4769-829a-4344-b395-f891afaf59f7
-- title:
--   §4.1, display (1), p. 11 — both firms message expected group-b consumers: F(p) = 1/α − (1−α)/(αp) on [1−α, 1] is a symmetric equilibrium, profit α(1−α)
-- statement:
--   Consider the pricing subgame in which both firms target the high-valuation group $b$ and message only the consumers they expect to be in group $b$. Then a mass $\alpha^2$ of group-$b$ consumers are shoppers and each firm has a mass $\alpha(1-\alpha)$ of loyal consumers.
--
--   Let $1/2 < \alpha < 1$ and let $F$ be the cdf of display (1),
--   $$
--   F(p) = \frac1\alpha - \frac{1-\alpha}{\alpha p}\quad\text{for } p \in [1-\alpha, 1],
--   $$
--   with $F = 0$ below $1 - \alpha$ and $F = 1$ above $1$. Then:
--
--   1. there is a probability measure on $\mathbb R$ whose cdf is $F$;
--   2. for every probability measure $\mu$ with cdf $F$, the profile in which both firms draw their prices from $\mu$ is a Nash equilibrium of the pricing subgame, and each firm's expected profit is
--   $$
--   U_1 = U_2 = \alpha(1-\alpha).
--   $$
--
--   This is the pricing equilibrium of the high-cost case and of the configuration b(1)b(1); it also supplies the off-path subgame in which a firm deviates to messaging only its expected group.
--
--   **Formalization Note** The paper's profit "$\alpha(1-\alpha) - c$" includes the sunk messaging cost; the statement gives the pricing-stage profit, which is where $c$ does not enter. The case $\alpha = 1$ is excluded: there $1 - \alpha = 0$ and $F$ degenerates (the subgame is Bertrand competition). The parameter $A$ plays no role (both firms serve group $b$) and is kept only for the uniform signature.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 10 (expected profit display, §4.1) and p. 11, display (1)

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

theorem display1_symmetric_equilibrium (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α < 1) :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ⇑(ProbabilityTheory.cdf μ) = Fcdf α) ∧
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → ⇑(ProbabilityTheory.cdf μ) = Fcdf α →
      IsPricingNE A α ((.b, .expected), (.b, .expected)) μ μ ∧
      U₁ A α ((.b, .expected), (.b, .expected)) μ μ = α * (1 - α) ∧
      U₂ A α ((.b, .expected), (.b, .expected)) μ μ = α * (1 - α) := by sorry
end ImperfectTargeting.CostlessAds
