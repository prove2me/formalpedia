-- Prove2me | Theorems.Thm_ImpactInvesting_Portfolio_induced_residual_indep
-- name    : ImpactInvesting.Portfolio.induced_residual_indep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:40.893447+00:00
-- url     : https://prove2.me/theorems/33ba9023-1537-41d1-b296-bf316c9e7863
-- title:
--   (A.22), p. 65 — α_[i:N] = ρσ_α X_{i:N} + e_[i]; the X_{i:N} are independent of the e_[i]
-- statement:
--   Assume (A1) with the normalisations $\mu_x = \mu_\alpha = 0$, $\sigma_x = 1$, let $\sigma_\alpha > 0$, $-1 < \rho < 1$, and let $e_i = \alpha_i - \rho\sigma_\alpha X_i$ be the residuals of (A.21). Write $X_{i:N}$ for the order statistics of $X_1,\dots,X_N$ and $\alpha_{[i:N]}$, $e_{[i]}$ for the entries of $\alpha$ and $e$ attached to the security of rank $i$ by $X$. Then
--
--   1. for every rank $i$, pointwise,
--   $$\alpha_{[i:N]} = \rho\,\sigma_\alpha X_{i:N} + e_{[i]};$$
--   2. the random vector $(X_{1:N}, \dots, X_{N:N})$ is independent of the random vector $(e_{[1]}, \dots, e_{[N]})$.
--
--   Item 1 is display (A.22) under the normalisations and item 2 is the sentence that follows it.
--
--   **Formalization Note.** Ranks are 0-based (`i : Fin N` is rank $i+1$). The vectors are `Fin N → ℝ`-valued random variables; independence is `IndepFun`.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 65, Appendix B.2, proof of Proposition 2, (A.22) and the following sentence; used in (A.24)–(A.25), p. 66

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

open MeasureTheory ProbabilityTheory

namespace ImpactInvesting.Portfolio

theorem induced_residual_indep {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1) :
    (∀ i, inducedOrderStatRV X α i = fun ω => ρ * σα * orderStatRV X i ω +
        inducedOrderStatRV X (fun j ω => α j ω - ρ * σα * X j ω) i ω) ∧
    IndepFun (fun ω i => orderStatRV X i ω)
      (fun ω i => inducedOrderStatRV X (fun j ω => α j ω - ρ * σα * X j ω) i ω) P := by sorry

end ImpactInvesting.Portfolio
