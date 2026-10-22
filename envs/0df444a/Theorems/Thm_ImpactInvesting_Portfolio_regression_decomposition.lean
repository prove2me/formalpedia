-- Prove2me | Theorems.Thm_ImpactInvesting_Portfolio_regression_decomposition
-- name    : ImpactInvesting.Portfolio.regression_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:41.704062+00:00
-- url     : https://prove2.me/theorems/7ec7b5c3-3945-4ebb-b5b8-b2eeeaea3590
-- title:
--   (A.21), p. 65 — α_i = ρσ_α X_i + e_i with e_i ~ N(0, σ_α²(1−ρ²)) and X_1,…,X_N, e_1,…,e_N mutually independent
-- statement:
--   Assume (A1) with the normalisations $\mu_x = \mu_\alpha = 0$, $\sigma_x = 1$, and let $\sigma_\alpha > 0$, $-1 < \rho < 1$. Define the regression residuals
--   $$e_i = \alpha_i - \rho\,\sigma_\alpha X_i, \qquad i = 1, \dots, N,$$
--   so that $\alpha_i = \rho\sigma_\alpha X_i + e_i$, which is display (A.21) under the normalisations. Then
--
--   1. each $e_i$ is normal with mean $0$ and variance $\sigma_\alpha^2(1-\rho^2)$;
--   2. the $2N$ random variables $X_1,\dots,X_N, e_1,\dots,e_N$ are mutually independent.
--
--   This is the first step of the paper's proof of Proposition 2: it separates the part of the excess return explained by the impact factor from a residual independent of all impact factors.
--
--   **Formalization Note.** The law of $e_i$ is stated as `P.map (e i) = gaussianReal 0 (σα^2 (1-ρ^2))`. Mutual independence of the $2N$ variables is `iIndepFun` over the index type `Fin N ⊕ Fin N` (left copy: $X_i$, right copy: $e_i$). Indices are 0-based.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 65, Appendix B.2, proof of Proposition 2, (A.21)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

theorem regression_decomposition {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1) :
    (∀ i, P.map (fun ω => α i ω - ρ * σα * X i ω) =
        gaussianReal 0 (σα ^ 2 * (1 - ρ ^ 2)).toNNReal) ∧
    iIndepFun (fun k : Fin N ⊕ Fin N =>
        Sum.elim (fun i => X i) (fun i ω => α i ω - ρ * σα * X i ω) k) P := by sorry

end ImpactInvesting.Portfolio
