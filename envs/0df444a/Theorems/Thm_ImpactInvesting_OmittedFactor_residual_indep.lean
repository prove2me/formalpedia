-- Prove2me | Theorems.Thm_ImpactInvesting_OmittedFactor_residual_indep
-- name    : ImpactInvesting.OmittedFactor.residual_indep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:19.881417+00:00
-- url     : https://prove2.me/theorems/2a0b2b55-c05f-451e-b320-f79e826a8f9d
-- title:
--   Appendix B.5, (A.42)–(A.43), p. 68 — λ − PX is independent of X, with P = aI + bL
-- statement:
--   Assume (A2) with $\mu_x = 0$, $\sigma_x = 1$, $\sigma_\lambda > 0$ and $\rho_x < 1$, and let $\rho_{adj} = (\rho_{x,\lambda} - \tilde\rho_{x,\lambda})/(1-\rho_x)$. Put
--   $$a = \rho_{adj}\,\sigma_\lambda, \qquad b = \Big(\frac{\rho_{x,\lambda} + (N-1)\tilde\rho_{x,\lambda}}{1 + (N-1)\rho_x} - \rho_{adj}\Big)\sigma_\lambda,$$
--   and let $\mathbf P = a\mathbf I + b\mathbf L$, where $\mathbf L = \mathbf 1\mathbf 1^{\mathsf T}/N$ is the $N\times N$ matrix with all entries $1/N$, so that $(\mathbf P X)_i = aX_i + b\bar X$ with $\bar X = \frac1N\sum_{j} X_j$. Then the residual vector
--   $$\lambda - \mathbf P X = \big(\lambda_i - aX_i - b\bar X\big)_{i=1}^N$$
--   is independent of $X$.
--
--   This is the regression decomposition behind Proposition 5: $\lambda = \mathbf P X + (\lambda - \mathbf P X)$ splits $\lambda$ into a function of $X$ and a Gaussian residual independent of $X$, which is what makes the induced order statistics $\lambda_{[i:N]}$ computable from the order statistics of $X$.
--
--   **Formalization Note** The page writes $n$ for $N$ in $(n-1)$; the statement uses $N$. When $1 + (N-1)\rho_x = 0$ the mean $\bar X$ vanishes almost surely and the statement holds for any $b$ (Lean's convention $x/0 = 0$ included), so no hypothesis excludes that case. Independence is Mathlib's `IndepFun` of the two $\mathbb R^N$-valued maps.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 68, Appendix B.5, proof of Proposition 5, (A.42), (A.43)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_OmittedFactor_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.OmittedFactor
theorem residual_indep {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X lam : Fin N → Ω → ℝ) (μlam σlam ρxlam ρx ρlam ρxlamt : ℝ)
    (hA2 : IsA2 P X lam μlam σlam ρxlam ρx ρlam ρxlamt) (hσ : 0 < σlam) (hρx : ρx < 1) :
    IndepFun
      (fun ω i => lam i ω - rhoAdj ρxlam ρx ρxlamt * σlam * X i ω
        - ((ρxlam + ((N : ℝ) - 1) * ρxlamt) / (1 + ((N : ℝ) - 1) * ρx) - rhoAdj ρxlam ρx ρxlamt) * σlam
          * ((1 / (N : ℝ)) * ∑ j, X j ω))
      (fun ω i => X i ω) P := by sorry
end ImpactInvesting.OmittedFactor
