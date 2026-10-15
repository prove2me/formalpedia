-- Prove2me | Theorems.Thm_ImpactInvesting_OmittedFactor_proposition_5
-- name    : ImpactInvesting.OmittedFactor.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:16.783622+00:00
-- url     : https://prove2.me/theorems/ab59dbac-763d-47c8-b0d1-25ad03e9c57b
-- title:
--   Proposition 5, pp. 19–20 — mean, variance and covariances of impact-ranked omitted-factor returns λ_[i:N] under (A2), (27) corrected
-- statement:
--   Let $X = (X_1,\dots,X_N)$ be the impact factors and $\lambda = (\lambda_1,\dots,\lambda_N)$ the omitted-factor returns of $N$ securities, and assume (A2): $(X, \lambda)$ is jointly Gaussian with $\mathbb E[X_i] = 0$, $\mathrm{Var}(X_i) = 1$, $\mathbb E[\lambda_i] = \mu_\lambda$, $\mathrm{Var}(\lambda_i) = \sigma_\lambda^2 > 0$, $\mathrm{Corr}(X_i, \lambda_i) = \rho_{x,\lambda}$, and, for $i \ne j$, $\mathrm{Corr}(X_i, X_j) = \rho_x < 1$, $\mathrm{Corr}(\lambda_i, \lambda_j) = \rho_\lambda$, $\mathrm{Corr}(X_i, \lambda_j) = \tilde\rho_{x,\lambda}$. Let
--   $$\rho_{adj} = \frac{\rho_{x,\lambda} - \tilde\rho_{x,\lambda}}{1 - \rho_x}.$$
--   Write $X_{i:N}$ for the $i$-th order statistic of $X$ and $\lambda_{[i:N]}$ for the $i$-th induced order statistic of $\lambda$, the order being induced by $X$. Then:
--
--   1. for every $i$, $\;\mathbb E[\lambda_{[i:N]}] - \mu_\lambda = \rho_{adj}\sigma_\lambda\,\mathbb E[X_{i:N}]$;
--   2. for every $i$, $\;\mathrm{Var}(\lambda_{[i:N]}) = \sigma_\lambda^2\big(1 - \rho_{adj}^2 + \rho_{adj}^2\mathrm{Var}(X_{i:N})\big)$;
--   3. for every $i \ne j$,
--   $$\mathrm{Cov}\big(\lambda_{[i:N]}, \lambda_{[j:N]}\big) = \sigma_\lambda^2\rho_{adj}^2\,\mathrm{Cov}(X_{i:N}, X_{j:N}) + \sigma_\lambda^2\big(\rho_\lambda - \rho_x\rho_{adj}^2\big).$$
--
--   Proposition 5 shows that when an investor ranks securities by an impact factor while ignoring some priced factors, the ranked securities earn apparent excess returns governed by the adjusted correlation between the impact factor and the omitted factors: a selection rule correlated with an omitted factor produces nonzero "alpha" even without mispricing.
--
--   **Formalization Note** Item 3 corrects a printed slip: the paper writes the last term as $(\rho_\lambda - \rho_x\rho_{adj}^2)$ without the factor $\sigma_\lambda^2$. Replacing $\lambda$ by $c\lambda$ with $c > 0$ multiplies the left side by $c^2$ and leaves every correlation unchanged, so the printed form fails unless $\sigma_\lambda = 1$. (A2) is read as joint Gaussianity of $(X,\lambda)$, as in the proof (A.40). The normalisations $\mu_x = 0$, $\sigma_x = 1$ are hypotheses; $\sigma_\lambda > 0$ and $\rho_x < 1$ (implicit in (24)) are explicit. Ranks are 0-based in Lean; ties in the sort are broken by index and occur with probability zero.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), pp. 19–20, Proposition 5, (24)–(27)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_OmittedFactor_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.OmittedFactor
theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X lam : Fin N → Ω → ℝ) (μlam σlam ρxlam ρx ρlam ρxlamt : ℝ)
    (hA2 : IsA2 P X lam μlam σlam ρxlam ρx ρlam ρxlamt) (hσ : 0 < σlam) (hρx : ρx < 1) :
    (∀ i : Fin N, P[ImpactInvesting.Portfolio.inducedOrderStatRV X lam i] - μlam
        = rhoAdj ρxlam ρx ρxlamt * σlam * P[ImpactInvesting.Portfolio.orderStatRV X i]) ∧
    (∀ i : Fin N, Var[ImpactInvesting.Portfolio.inducedOrderStatRV X lam i; P]
        = σlam ^ 2 * (1 - rhoAdj ρxlam ρx ρxlamt ^ 2
            + rhoAdj ρxlam ρx ρxlamt ^ 2 * Var[ImpactInvesting.Portfolio.orderStatRV X i; P])) ∧
    (∀ i j : Fin N, i ≠ j →
        cov[ImpactInvesting.Portfolio.inducedOrderStatRV X lam i, ImpactInvesting.Portfolio.inducedOrderStatRV X lam j; P]
          = σlam ^ 2 * rhoAdj ρxlam ρx ρxlamt ^ 2 * cov[ImpactInvesting.Portfolio.orderStatRV X i, ImpactInvesting.Portfolio.orderStatRV X j; P]
            + σlam ^ 2 * (ρlam - ρx * rhoAdj ρxlam ρx ρxlamt ^ 2)) := by sorry
end ImpactInvesting.OmittedFactor
