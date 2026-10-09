-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_2_22_stoch
-- name    : NonconvexAG.Stoch.eq_2_22_stoch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:31.402112+00:00
-- url     : https://prove2.me/theorems/34fd90d9-6125-4934-910f-bf57494ffa8e
-- title:
--   Stochastic analogue of (2.22) — α_k⟨G(x^md_k, ξ_k), x_{k−1} − x⟩ identity (p. 17)
-- statement:
--   Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any oracle and any noise sequence; let $g$ be any map $\mathbb R^n\to\mathbb R^n$ (in the paper $g=\nabla\Psi$) and $\delta_k=G(x^{md}_k,\xi_k)-g(x^{md}_k)$. Then for every sample point, every $k\ge1$ and every $x\in\mathbb R^n$,
--   $$\alpha_k\langle g(x^{md}_k)+\delta_k,\,x_{k-1}-x\rangle=\frac{\alpha_k}{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2\Big]+\frac{\alpha_k\lambda_k}{2}\|g(x^{md}_k)+\delta_k\|^2 .$$
--
--   It is the three-point identity for the step (3.2), $x_k=x_{k-1}-\lambda_kG(x^{md}_k,\xi_k)$, which produces the telescoping distance terms of the convex analysis.
--
--   **Formalization Note** The identity is pathwise; $g(x^{md}_k)+\delta_k$ is the oracle output $G(x^{md}_k,\xi_k)$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 17, §3.1, display "Similar to (2.22)"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The stochastic analogue of (2.22) (proof of Theorem 3 b), p. 17, display "Similar to
(2.22)"), pathwise for every sample point `ω`, every `k ≥ 1` and every `x ∈ ℝⁿ`:
`αₖ⟨∇Ψ(x^md_k) + δₖ, x_{k−1} − x⟩ = (αₖ/(2λₖ))[‖x_{k−1} − x‖² − ‖xₖ − x‖²]
  + (αₖλₖ/2)‖∇Ψ(x^md_k) + δₖ‖²`. -/
theorem eq_2_22_stoch {n : ℕ} (g : E n → E n)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω, ∀ x : E n,
      α k * ⟪g (xmdSeq G α β lam x0 ξ k ω) + delta G g α β lam x0 ξ k ω,
          xSeq G α β lam x0 ξ (k - 1) ω - x⟫_ℝ =
        α k / (2 * lam k) *
            (‖xSeq G α β lam x0 ξ (k - 1) ω - x‖ ^ 2 - ‖xSeq G α β lam x0 ξ k ω - x‖ ^ 2)
          + α k * lam k / 2 *
              ‖g (xmdSeq G α β lam x0 ξ k ω) + delta G g α β lam x0 ξ k ω‖ ^ 2 := by sorry

end NonconvexAG.Stoch
