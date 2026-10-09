-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_one_step
-- name    : NonconvexAG.Stoch.one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:22:52.555958+00:00
-- url     : https://prove2.me/theorems/f9488d40-6ce2-48b7-90e8-5bcf1edbd4f1
-- title:
--   One-step descent of the RSAG method (proof of Theorem 3 a), p. 16)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient $\nabla\Psi$. Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any oracle $G$ and any noise sequence, and write $\delta_k=G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)$. Then for every sample point and every $k\ge1$,
--   $$\Psi(x_k)\le\Psi(x_{k-1})-\lambda_k(1-L_\Psi\lambda_k)\|\nabla\Psi(x^{md}_k)\|^2+\frac{L_\Psi(1-\alpha_k)^2}{2}\|x^{ag}_{k-1}-x_{k-1}\|^2+\frac{L_\Psi\lambda_k^2}{2}\|\delta_k\|^2-\lambda_k\big\langle\nabla\Psi(x_{k-1})-L_\Psi\lambda_k\nabla\Psi(x^{md}_k),\delta_k\big\rangle .$$
--
--   This is the stochastic counterpart of (2.15): the descent of the long-step sequence $x_k$ in one iteration, with the oracle error appearing through a quadratic term and a linear term that vanishes in conditional expectation.
--
--   **Formalization Note** The inequality is pathwise: it holds for every realization of the noise, so no probabilistic assumption is made. It is the outer ends of the paper's chain (the second display of the proof).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 16, §3.1, proof of Theorem 3 a), second display

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- One-step descent of the RSAG method (proof of Theorem 3 a), p. 16, second display, outer
ends), pathwise for every sample point `ω` and every `k ≥ 1`, with
`δₖ = G(x^md_k, ξₖ) − ∇Ψ(x^md_k)`:
`Ψ(xₖ) ≤ Ψ(xₖ₋₁) − λₖ(1 − L_Ψλₖ)‖∇Ψ(x^md_k)‖² + (L_Ψ(1 − αₖ)²/2)‖x^ag_{k−1} − xₖ₋₁‖²
  + (L_Ψλₖ²/2)‖δₖ‖² − λₖ⟨∇Ψ(xₖ₋₁) − L_Ψλₖ∇Ψ(x^md_k), δₖ⟩`. -/
theorem one_step {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω,
      Ψ (xSeq G α β lam x0 ξ k ω) ≤
        Ψ (xSeq G α β lam x0 ξ (k - 1) ω)
          - lam k * (1 - LΨ * lam k) * ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2
          + LΨ * (1 - α k) ^ 2 / 2 *
              ‖xagSeq G α β lam x0 ξ (k - 1) ω - xSeq G α β lam x0 ξ (k - 1) ω‖ ^ 2
          + LΨ * lam k ^ 2 / 2 * ‖delta G g α β lam x0 ξ k ω‖ ^ 2
          - lam k * ⟪g (xSeq G α β lam x0 ξ (k - 1) ω)
                - (LΨ * lam k) • g (xmdSeq G α β lam x0 ξ k ω),
              delta G g α β lam x0 ξ k ω⟫_ℝ := by sorry

end NonconvexAG.Stoch
