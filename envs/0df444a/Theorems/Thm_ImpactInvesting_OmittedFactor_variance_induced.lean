-- Prove2me | Theorems.Thm_ImpactInvesting_OmittedFactor_variance_induced
-- name    : ImpactInvesting.OmittedFactor.variance_induced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:17.723428+00:00
-- url     : https://prove2.me/theorems/e22c28a6-af2a-4906-b987-1e5ea03aa44a
-- title:
--   (26), p. 20 — Var(λ_[i:N]) = σ_λ²(1 − ρ_adj² + ρ_adj² Var(X_{i:N}))
-- statement:
--   Assume (A2) with $\mu_x = 0$, $\sigma_x = 1$, $\sigma_\lambda > 0$ and $\rho_x < 1$, and let $\rho_{adj} = (\rho_{x,\lambda} - \tilde\rho_{x,\lambda})/(1-\rho_x)$. Then for every rank $i = 1,\dots,N$,
--   $$\mathrm{Var}\big(\lambda_{[i:N]}\big) = \sigma_\lambda^2\big(1 - \rho_{adj}^2 + \rho_{adj}^2\,\mathrm{Var}(X_{i:N})\big).$$
--
--   This is display (26) of Proposition 5: ranking by $X$ changes the variance of the omitted-factor return only through the variance of the corresponding order statistic of $X$, weighted by $\rho_{adj}^2$.
--
--   **Formalization Note** Ranks are 0-based in Lean. Variances are Mathlib's `variance`; every variable involved is square-integrable under the Gaussian model.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 20, Proposition 5, (26)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_OmittedFactor_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.OmittedFactor
theorem variance_induced {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X lam : Fin N → Ω → ℝ) (μlam σlam ρxlam ρx ρlam ρxlamt : ℝ)
    (hA2 : IsA2 P X lam μlam σlam ρxlam ρx ρlam ρxlamt) (hσ : 0 < σlam) (hρx : ρx < 1) :
    ∀ i : Fin N, Var[ImpactInvesting.Portfolio.inducedOrderStatRV X lam i; P]
      = σlam ^ 2 * (1 - rhoAdj ρxlam ρx ρxlamt ^ 2
          + rhoAdj ρxlam ρx ρxlamt ^ 2 * Var[ImpactInvesting.Portfolio.orderStatRV X i; P]) := by sorry
end ImpactInvesting.OmittedFactor
