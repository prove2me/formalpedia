-- Prove2me | Theorems.Thm_ImpactInvesting_Portfolio_proposition_2_mean
-- name    : ImpactInvesting.Portfolio.proposition_2_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:42.992799+00:00
-- url     : https://prove2.me/theorems/2ec5b01c-aaba-423f-8fae-757b95aad13f
-- title:
--   Proposition 2 (8), p. 14 — E[α_[i:N]] = ρσ_α E[X_{i:N}]
-- statement:
--   Assume (A1) with the normalisations $\mu_x = \mu_\alpha = 0$, $\sigma_x = 1$, and let $\sigma_\alpha > 0$, $-1 < \rho < 1$. For every rank $i \in \{1,\dots,N\}$, the expected value of the $i$-th induced order statistic is
--   $$\mu_i \equiv \mathbb E\big[\alpha_{[i:N]}\big] = \rho\,\sigma_\alpha\,\mathbb E[X_{i:N}],$$
--   where $X_{i:N}$ is the $i$-th order statistic of the standard normal sample $X_1,\dots,X_N$ and $\alpha_{[i:N]}$ is the excess return of the security of rank $i$ by $X$.
--
--   The expected alpha of a ranked security is thus the product of the correlation $\rho$, the dispersion $\sigma_\alpha$ of alphas, and a standardised score $\mathbb E[X_{i:N}]$ depending only on the rank.
--
--   **Formalization Note.** Ranks are 0-based (`i : Fin N` is rank $i+1$). The normalisation $\mu_\alpha = 0$ is essential: without it the right-hand side gains $\mu_\alpha$ (display (A.23)).
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 14, Proposition 2, (8)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

theorem proposition_2_mean {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1) (i : Fin N) :
    P[inducedOrderStatRV X α i] = ρ * σα * P[orderStatRV X i] := by sorry

end ImpactInvesting.Portfolio
