-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_2_17_stoch
-- name    : NonconvexAG.Stoch.eq_2_17_stoch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:15.954505+00:00
-- url     : https://prove2.me/theorems/9f7e4120-2f6b-4044-ab9c-5b4920287b4f
-- title:
--   Stochastic analogue of (2.17) — ‖x^ag_{k−1} − x_{k−1}‖² ≤ Γ_{k−1} Σ_τ ((λ_τ − β_τ)²/(Γ_τα_τ))‖∇Ψ(x^md_τ) + δ_τ‖² (p. 16)
-- statement:
--   Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any oracle $G$ and any noise sequence; let $g$ be any map $\mathbb R^n\to\mathbb R^n$ (in the paper $g=\nabla\Psi$) and $\delta_\tau=G(x^{md}_\tau,\xi_\tau)-g(x^{md}_\tau)$. Then for every sample point and every $k\ge1$,
--   $$\|x^{ag}_{k-1}-x_{k-1}\|^2\le\Gamma_{k-1}\sum_{\tau=1}^{k-1}\frac{(\lambda_\tau-\beta_\tau)^2}{\Gamma_\tau\alpha_\tau}\Big[\|g(x^{md}_\tau)\|^2+\|\delta_\tau\|^2+2\langle g(x^{md}_\tau),\delta_\tau\rangle\Big].$$
--
--   It bounds the gap between the two sequences of the method by the past stochastic gradients $G(x^{md}_\tau,\xi_\tau)=g(x^{md}_\tau)+\delta_\tau$; combined with the one-step inequality it yields the summed bound of the proof of Theorem 3 a).
--
--   **Formalization Note** The inequality is pathwise. At $k=1$ both sides are $0$. The paper prints $\|\nabla\Psi(x^{md}_\tau)+\delta_k\|^2$ in the first line of its display; the index of $\delta$ there is $\tau$, as the second line of the same display shows, and the Lean states the second line.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 16, §3.1, display "Noting that similar to (2.17)"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The stochastic analogue of (2.17) (proof of Theorem 3 a), p. 16, display "Noting that
similar to (2.17)", outer ends, with the printed `δₖ` inside the first sum read as `δ_τ`),
pathwise for every sample point `ω` and every `k ≥ 1`:
`‖x^ag_{k−1} − x_{k−1}‖² ≤ Γ_{k−1} Σ_{τ=1}^{k−1} ((λ_τ − β_τ)²/(Γ_τα_τ))
  [‖∇Ψ(x^md_τ)‖² + ‖δ_τ‖² + 2⟨∇Ψ(x^md_τ), δ_τ⟩]`. -/
theorem eq_2_17_stoch {n : ℕ} (g : E n → E n)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω,
      ‖xagSeq G α β lam x0 ξ (k - 1) ω - xSeq G α β lam x0 ξ (k - 1) ω‖ ^ 2 ≤
        NonconvexAG.Smooth.Gamma α (k - 1) * ∑ τ ∈ Finset.Icc 1 (k - 1),
          (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) *
            (‖g (xmdSeq G α β lam x0 ξ τ ω)‖ ^ 2 + ‖delta G g α β lam x0 ξ τ ω‖ ^ 2
              + 2 * ⟪g (xmdSeq G α β lam x0 ξ τ ω), delta G g α β lam x0 ξ τ ω⟫_ℝ) := by sorry

end NonconvexAG.Stoch
