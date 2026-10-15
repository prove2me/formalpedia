-- Prove2me | Theorems.Thm_ImpactInvesting_OmittedFactor_expected_induced
-- name    : ImpactInvesting.OmittedFactor.expected_induced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:13.055679+00:00
-- url     : https://prove2.me/theorems/167d70d0-a3c4-4929-99a7-8a23d38191b7
-- title:
--   Appendix B.5, (A.44) = (25), p. 68 — E[λ_[i:N]] = μ_λ + ρ_adj σ_λ E[X_{i:N}]
-- statement:
--   Assume (A2) with $\mu_x = 0$, $\sigma_x = 1$, $\sigma_\lambda > 0$ and $\rho_x < 1$, and let $\rho_{adj} = (\rho_{x,\lambda} - \tilde\rho_{x,\lambda})/(1-\rho_x)$. Then for every rank $i = 1,\dots,N$ the induced order statistic $\lambda_{[i:N]}$ (the omitted-factor return of the security of $i$-th smallest impact factor) has mean
--   $$\mathbb E\big[\lambda_{[i:N]}\big] = \mu_\lambda + \rho_{adj}\,\sigma_\lambda\,\mathbb E[X_{i:N}].$$
--
--   The apparent alpha of the security ranked $i$-th by impact is thus the omitted-factor premium $\mu_\lambda$ plus a term proportional to the adjusted correlation; it is display (25) of Proposition 5, obtained in the proof as (A.44).
--
--   **Formalization Note** Ranks are 0-based in Lean (rank $i$ is the paper's $i+1$). Expectations are Bochner integrals; every variable involved is integrable under the Gaussian model.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 68, Appendix B.5, proof of Proposition 5, (A.44); p. 19, (25)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_OmittedFactor_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.OmittedFactor
theorem expected_induced {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X lam : Fin N → Ω → ℝ) (μlam σlam ρxlam ρx ρlam ρxlamt : ℝ)
    (hA2 : IsA2 P X lam μlam σlam ρxlam ρx ρlam ρxlamt) (hσ : 0 < σlam) (hρx : ρx < 1) :
    ∀ i : Fin N, P[ImpactInvesting.Portfolio.inducedOrderStatRV X lam i]
      = μlam + rhoAdj ρxlam ρx ρxlamt * σlam * P[ImpactInvesting.Portfolio.orderStatRV X i] := by sorry
end ImpactInvesting.OmittedFactor
