-- Prove2me | Theorems.Thm_ImpactInvesting_Portfolio_proposition_2_cov
-- name    : ImpactInvesting.Portfolio.proposition_2_cov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:44.284186+00:00
-- url     : https://prove2.me/theorems/cf9066ac-74a1-4fcb-b006-330d8c5fade0
-- title:
--   Proposition 2 (10), p. 14 — Cov(α_[i:N], α_[j:N]) = σ_α²ρ²Cov(X_{i:N}, X_{j:N}) for i ≠ j
-- statement:
--   Assume (A1) with the normalisations $\mu_x = \mu_\alpha = 0$, $\sigma_x = 1$, and let $\sigma_\alpha > 0$, $-1 < \rho < 1$. For distinct ranks $i \ne j$ in $\{1,\dots,N\}$, the covariance of the induced order statistics is
--   $$\sigma_{ij} \equiv \operatorname{Cov}\big(\alpha_{[i:N]}, \alpha_{[j:N]}\big) = \sigma_\alpha^2\rho^2 \operatorname{Cov}(X_{i:N}, X_{j:N}),$$
--   where $X_{i:N}, X_{j:N}$ are order statistics of the standard normal sample $X_1,\dots,X_N$.
--
--   Ranking by $X$ makes the otherwise independent alphas correlated; the residuals contribute nothing to the covariance.
--
--   **Formalization Note.** Ranks are 0-based (`i j : Fin N` are ranks $i+1, j+1$). Covariance is Mathlib's `cov[·, ·; P]`.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 14, Proposition 2, (10)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

theorem proposition_2_cov {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1) (i j : Fin N) (hij : i ≠ j) :
    cov[inducedOrderStatRV X α i, inducedOrderStatRV X α j; P] =
      σα ^ 2 * ρ ^ 2 * cov[orderStatRV X i, orderStatRV X j; P] := by sorry

end ImpactInvesting.Portfolio
