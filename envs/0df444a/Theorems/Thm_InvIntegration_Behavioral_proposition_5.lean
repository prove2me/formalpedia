-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_proposition_5
-- name    : InvIntegration.Behavioral.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:41.379638+00:00
-- url     : https://prove2.me/theorems/42208ce7-eab5-456e-be52-877d325af4e7
-- title:
--   Proposition 5 (ii)–(iii), p. 14 (PDF 14) (corrected: Π(µ,σ) > 0) — the behavioral value of integration is positive iff ρ < ρ̄, and iff σ < σ̄
-- statement:
--   Let $v^*_m(\sigma)$ be the equilibrium threshold valuation of the multichannel market $N(\mu,\sigma^2)$ for $\sigma>0$, and $v^*_I(\rho,\sigma)$ that of the integrated market $N(2\mu,2(1+\rho)\sigma^2)$ for $\rho\in(-1,1)$, $\sigma>0$. Let
--   $$\mathrm{BV}(\rho,\sigma) = \frac{G(v^*_m(\sigma))-G(v^*_I(\rho,\sigma))}{\bar G(v^*_m(\sigma))}\times\frac{\Pi\bigl(2\mu,\sqrt{2(1+\rho)}\,\sigma\bigr)}{2\Pi(\mu,\sigma)}$$
--   be the behavioral value of integration (the second term of (6)), and $\sigma_{\max}=\mu(p-c)/((p-s)\phi(\hat z))$, so that $\Pi(\mu,\sigma)>0$ exactly for $\sigma<\sigma_{\max}$. Then:
--   1. **(ii)** For every $\sigma>0$ with $\Pi(\mu,\sigma)>0$ there is a unique $\bar\rho\in[-1,1]$ such that, for all $\rho\in(-1,1)$,
--   $$\mathrm{BV}(\rho,\sigma)>0 \iff \rho<\bar\rho .$$
--   2. **(iii)** For every $\rho\in(-1,1)$ there is a unique $\bar\sigma\in[0,\sigma_{\max}]$ such that, for all $\sigma\in(0,\sigma_{\max})$,
--   $$\mathrm{BV}(\rho,\sigma)>0 \iff \sigma<\bar\sigma .$$
--
--   The behavioral value is the part of the value of integration that comes from the change in consumers' strategic waiting. The theorem says integration helps through consumer behavior exactly when the markets are not too positively correlated and not too variable.
--
--   **Formalization Note.** This is the corrected statement. As printed, (iii) quantifies over all $\sigma>0$ and is false: with $p=10$, $c=2$, $s=0$, $\delta=0.7$, $G=U[0,20]$, $\rho=-0.5$, the behavioral value is $\le 0$ on an interval of $\sigma$ and positive again at $\sigma/\mu=2.86$, where $\Pi(\mu,\sigma)\approx-0.007<0$ and $v^*_m=10<v^*_I\approx10.71$. The paper's "possibly $\bar\rho=1$" and "possibly $\bar\sigma=\infty$" become $\bar\rho\in[-1,1]$ and $\bar\sigma\in[0,\sigma_{\max}]$; pinning these ranges makes "unique" meaningful. $v^*_m$ and $v^*_I$ are given as functions with the equilibrium property on the model's domain; by Proposition 3 they are the equilibrium valuations.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 14 (PDF 14), Proposition 5 (ii)–(iii) (corrected: Π(µ,σ) > 0)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem proposition_5 (P : Params) (hS : P.Standing)
    (vm : ℝ → ℝ) (hvm : ∀ σ : ℝ, 0 < σ → ∃ q ξ : ℝ, IsEquilibrium P P.μ σ q (vm σ) ξ)
    (vI : ℝ → ℝ → ℝ)
    (hvI : ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1, ∀ σ : ℝ, 0 < σ →
      ∃ q ξ : ℝ, IsEquilibrium P (2 * P.μ) (sdI σ ρ) q (vI ρ σ) ξ) :
    (∀ σ : ℝ, 0 < σ → 0 < Pi P P.μ σ →
      ∃! ρbar : ℝ, ρbar ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1,
        (0 < behavioralValue P σ ρ (vm σ) (vI ρ σ) ↔ ρ < ρbar)) ∧
    (∀ ρ ∈ Set.Ioo (-1 : ℝ) 1,
      ∃! σbar : ℝ, σbar ∈ Set.Icc 0 (sigmaMax P) ∧ ∀ σ ∈ Set.Ioo 0 (sigmaMax P),
        (0 < behavioralValue P σ ρ (vm σ) (vI ρ σ) ↔ σ < σbar)) := by sorry

end InvIntegration.Behavioral
