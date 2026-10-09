-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_3_10
-- name    : NonconvexAG.Stoch.eq_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:24:22.340389+00:00
-- url     : https://prove2.me/theorems/eb94c18b-342a-4574-b1f7-d1f4846e68e5
-- title:
--   (3.10), sign corrected — one-step bound on Ψ(x^ag_k) for convex Ψ (p. 17)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be convex and differentiable with $L_\Psi$-Lipschitz gradient. Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any oracle and any noise sequence, with $\delta_k=G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)$. Then for every sample point, every $k\ge1$ and every $x\in\mathbb R^n$,
--   $$\Psi(x^{ag}_k)\le(1-\alpha_k)\Psi(x^{ag}_{k-1})+\alpha_k\Psi(x)+\alpha_k\langle\nabla\Psi(x^{md}_k),x_{k-1}-x\rangle-\beta_k\|\nabla\Psi(x^{md}_k)\|^2-\beta_k\langle\nabla\Psi(x^{md}_k),\delta_k\rangle+\frac{L_\Psi\beta_k^2}{2}\|\nabla\Psi(x^{md}_k)+\delta_k\|^2 .$$
--
--   This is the one-step inequality for the aggregated sequence in the convex case, from which (3.11) is obtained by combining with the stochastic analogue of (2.22) and taking expectations.
--
--   **Formalization Note** The paper prints $+\beta_k\langle\nabla\Psi(x^{md}_k),\delta_k\rangle$ in (3.10) and in the line above it. By (3.3), $x^{ag}_k-x^{md}_k=-\beta_k(\nabla\Psi(x^{md}_k)+\delta_k)$, so $\langle\nabla\Psi(x^{md}_k),x^{ag}_k-x^{md}_k\rangle=-\beta_k\|\nabla\Psi(x^{md}_k)\|^2-\beta_k\langle\nabla\Psi(x^{md}_k),\delta_k\rangle$ and the printed sign is wrong pathwise; the Lean states the corrected sign. The error has mean zero and does not affect (3.11). The statement is pathwise.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 17, (3.10), sign of the ⟨∇Ψ(x^md_k), δ_k⟩ term corrected

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- (3.10), p. 17, with the sign of the inner-product term corrected: for convex `Ψ`, every
sample point `ω`, every `k ≥ 1` and every `x ∈ ℝⁿ`,
`Ψ(x^ag_k) ≤ (1 − αₖ)Ψ(x^ag_{k−1}) + αₖΨ(x) + αₖ⟨∇Ψ(x^md_k), x_{k−1} − x⟩
  − βₖ‖∇Ψ(x^md_k)‖² − βₖ⟨∇Ψ(x^md_k), δₖ⟩ + (L_Ψβₖ²/2)‖∇Ψ(x^md_k) + δₖ‖²`.
(The paper prints `+ βₖ⟨∇Ψ(x^md_k), δₖ⟩`; by (3.3) the sign is `−`.) -/
theorem eq_3_10 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hconv : ConvexOn ℝ Set.univ Ψ)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω, ∀ x : E n,
      Ψ (xagSeq G α β lam x0 ξ k ω) ≤
        (1 - α k) * Ψ (xagSeq G α β lam x0 ξ (k - 1) ω) + α k * Ψ x
          + α k * ⟪g (xmdSeq G α β lam x0 ξ k ω), xSeq G α β lam x0 ξ (k - 1) ω - x⟫_ℝ
          - β k * ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2
          - β k * ⟪g (xmdSeq G α β lam x0 ξ k ω), delta G g α β lam x0 ξ k ω⟫_ℝ
          + LΨ * β k ^ 2 / 2 *
              ‖g (xmdSeq G α β lam x0 ξ k ω) + delta G g α β lam x0 ξ k ω‖ ^ 2 := by sorry

end NonconvexAG.Stoch
