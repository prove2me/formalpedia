-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_2_21
-- name    : NonconvexAG.Stoch.eq_2_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:10.595969+00:00
-- url     : https://prove2.me/theorems/99d3c001-17fd-4fb2-96ed-3b247e3234de
-- title:
--   (2.21) along the RSAG run — Ψ(x^md_k) − [(1−α_k)Ψ(x^ag_{k−1}) + α_kΨ(x)] ≤ α_k⟨∇Ψ(x^md_k), x_{k−1} − x⟩
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be convex and differentiable with $L_\Psi$-Lipschitz gradient. Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any oracle and any noise sequence. Then for every sample point, every $k\ge1$ and every $x\in\mathbb R^n$,
--   $$\Psi(x^{md}_k)-\big[(1-\alpha_k)\Psi(x^{ag}_{k-1})+\alpha_k\Psi(x)\big]\le\alpha_k\langle\nabla\Psi(x^{md}_k),x_{k-1}-x\rangle .$$
--
--   It is the convexity step of the analysis: the middle point is the convex combination (2.2) of $x^{ag}_{k-1}$ and $x_{k-1}$, so the gradient inequality at $x^{md}_k$ compares it with that combination.
--
--   **Formalization Note** The statement is pathwise and uses only (2.2), which Algorithm 3 shares with Algorithm 1. It is the outer ends of the paper's chain (2.21).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 7, (2.21); used on p. 17 in the proof of Theorem 3 b)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- (2.21), p. 7 (outer ends of the chain), along the RSAG run: for convex `Ψ`, every sample
point `ω`, every `k ≥ 1` and every `x ∈ ℝⁿ`,
`Ψ(x^md_k) − [(1 − αₖ)Ψ(x^ag_{k−1}) + αₖΨ(x)] ≤ αₖ⟨∇Ψ(x^md_k), x_{k−1} − x⟩`. -/
theorem eq_2_21 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hconv : ConvexOn ℝ Set.univ Ψ)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω, ∀ x : E n,
      Ψ (xmdSeq G α β lam x0 ξ k ω)
          - ((1 - α k) * Ψ (xagSeq G α β lam x0 ξ (k - 1) ω) + α k * Ψ x) ≤
        α k * ⟪g (xmdSeq G α β lam x0 ξ k ω), xSeq G α β lam x0 ξ (k - 1) ω - x⟫_ℝ := by sorry

end NonconvexAG.Stoch
