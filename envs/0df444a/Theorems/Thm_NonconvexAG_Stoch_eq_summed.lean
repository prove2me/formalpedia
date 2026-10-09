-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_summed
-- name    : NonconvexAG.Stoch.eq_summed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:41.841446+00:00
-- url     : https://prove2.me/theorems/f799a8af-a325-4059-9240-6797fc50eaf3
-- title:
--   Summed RSAG descent with the martingale terms b_k (proof of Theorem 3 a), pp. 16–17)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient. Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any oracle and any noise sequence, with $\delta_k=G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)$, and let $C_k$ be the constants (2.7) for the horizon $N$. Then for every sample point and every $N$,
--   $$\Psi(x_N)\le\Psi(x_0)-\sum_{k=1}^N\lambda_kC_k\|\nabla\Psi(x^{md}_k)\|^2+\frac{L_\Psi}{2}\sum_{k=1}^N\lambda_k^2\Big(1+\frac{(\lambda_k-\beta_k)^2}{\alpha_k\Gamma_k\lambda_k^2}\sum_{\tau=k}^N\Gamma_\tau\Big)\|\delta_k\|^2-\sum_{k=1}^Nb_k,$$
--   where
--   $$b_k=\Big\langle\lambda_k\nabla\Psi(x_{k-1})-\Big[L_\Psi\lambda_k^2+\frac{L_\Psi(\lambda_k-\beta_k)^2}{\Gamma_k\alpha_k}\Big(\sum_{\tau=k}^N\Gamma_\tau\Big)\Big]\nabla\Psi(x^{md}_k),\ \delta_k\Big\rangle .$$
--
--   The three error terms are separated here: the gradient term with coefficients $\lambda_kC_k$, the variance term in $\|\delta_k\|^2$, and the terms $b_k$, which form a martingale difference sequence under Assumption 1.
--
--   **Formalization Note** The inequality is pathwise and holds for every $N\ge0$ (at $N=0$ it is an equality of $\Psi(x_0)$ with itself). The paper prints a chain whose middle line carries the sign "$-\frac{L_\Psi}{2}\sum\Gamma_k\sum\dots$"; that sign should be $+$, and the final line, which is what the Lean states, is correct.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, pp. 16–17, §3.1, display "Summing up the above inequalities" and the definition of b_k

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The summed inequality of the proof of Theorem 3 a) (pp. 16–17, display "Summing up the above
inequalities", outer ends), pathwise for every sample point `ω` and every horizon `N`:
`Ψ(x_N) ≤ Ψ(x₀) − Σ_{k=1}^N λₖCₖ‖∇Ψ(x^md_k)‖²
  + (L_Ψ/2) Σ_{k=1}^N λₖ²(1 + ((λₖ − βₖ)²/(αₖΓₖλₖ²)) Σ_{τ=k}^N Γ_τ)‖δₖ‖² − Σ_{k=1}^N bₖ`, where
`bₖ = ⟨λₖ∇Ψ(xₖ₋₁) − [L_Ψλₖ² + (L_Ψ(λₖ − βₖ)²/(Γₖαₖ)) Σ_{τ=k}^N Γ_τ] ∇Ψ(x^md_k), δₖ⟩` and `Cₖ`
is (2.7) for the horizon `N`. -/
theorem eq_summed {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ N : ℕ, ∀ ω : Ω,
      Ψ (xSeq G α β lam x0 ξ N ω) ≤
        Ψ x0
          - ∑ k ∈ Finset.Icc 1 N,
              lam k * NonconvexAG.Smooth.C LΨ α β lam N k * ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2
          + LΨ / 2 * ∑ k ∈ Finset.Icc 1 N,
              lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
                  ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ) * ‖delta G g α β lam x0 ξ k ω‖ ^ 2
          - ∑ k ∈ Finset.Icc 1 N,
              ⟪lam k • g (xSeq G α β lam x0 ξ (k - 1) ω)
                  - (LΨ * lam k ^ 2 + LΨ * (lam k - β k) ^ 2 / (NonconvexAG.Smooth.Gamma α k * α k) *
                      ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ) • g (xmdSeq G α β lam x0 ξ k ω),
                delta G g α β lam x0 ξ k ω⟫_ℝ := by sorry

end NonconvexAG.Stoch
