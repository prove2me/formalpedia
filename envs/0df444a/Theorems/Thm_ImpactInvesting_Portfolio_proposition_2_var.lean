-- Prove2me | Theorems.Thm_ImpactInvesting_Portfolio_proposition_2_var
-- name    : ImpactInvesting.Portfolio.proposition_2_var
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:52.117779+00:00
-- url     : https://prove2.me/theorems/e15e4ba2-50f3-4414-b641-9c6da91a0112
-- title:
--   Proposition 2 (9), p. 14 — Var(α_[i:N]) = σ_α²(1 − ρ² + ρ²Var(X_{i:N}))
-- statement:
--   Assume (A1) with the normalisations $\mu_x = \mu_\alpha = 0$, $\sigma_x = 1$, and let $\sigma_\alpha > 0$, $-1 < \rho < 1$. For every rank $i \in \{1,\dots,N\}$, the variance of the $i$-th induced order statistic is
--   $$\sigma_i^2 \equiv \operatorname{Var}\big(\alpha_{[i:N]}\big) = \sigma_\alpha^2\big(1 - \rho^2 + \rho^2 \operatorname{Var}(X_{i:N})\big),$$
--   where $X_{i:N}$ is the $i$-th order statistic of the standard normal sample $X_1,\dots,X_N$.
--
--   The variance splits into a residual part $\sigma_\alpha^2(1-\rho^2)$, unaffected by ranking, and a part $\sigma_\alpha^2\rho^2\operatorname{Var}(X_{i:N})$ inherited from the order statistic.
--
--   **Formalization Note.** Ranks are 0-based (`i : Fin N` is rank $i+1$). Variance is Mathlib's `Var[·; P]`.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 14, Proposition 2, (9)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

theorem proposition_2_var {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1) (i : Fin N) :
    Var[inducedOrderStatRV X α i; P] = σα ^ 2 * (1 - ρ ^ 2 + ρ ^ 2 * Var[orderStatRV X i; P]) := by sorry

end ImpactInvesting.Portfolio
