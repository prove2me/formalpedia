-- Prove2me | Theorems.Thm_NonconvexAG_Smooth_eq_2_13
-- name    : NonconvexAG.Smooth.eq_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:43:37.978617+00:00
-- url     : https://prove2.me/theorems/ba1f0523-17b6-48a5-b2f5-4b704bdc7a0d
-- title:
--   (2.13) — ‖∇Ψ(x_{k−1}) − ∇Ψ(x^md_k)‖ ≤ L_Ψ(1 − α_k)‖x^ag_{k−1} − x_{k−1}‖
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $\|\nabla\Psi(y)-\nabla\Psi(x)\|\le L_\Psi\|y-x\|$ for all $x,y$, where $L_\Psi>0$. Run Algorithm 1 from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k>0$, $\lambda_k>0$. Then for every $k\ge1$, with $\Delta_k:=\nabla\Psi(x_{k-1})-\nabla\Psi(x^{md}_k)$,
--   $$\|\Delta_k\|\le L_\Psi(1-\alpha_k)\,\|x^{ag}_{k-1}-x_{k-1}\|.$$
--
--   It bounds the discrepancy between the gradient at the previous iterate and at the middle point, which enters the one-step descent estimate (2.15).
--
--   **Formalization Note** The statement is the outer ends of the chain (2.13). The gradient is the map `g` with `IsBetaSmooth Ψ g LΨ`.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 5, (2.13)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

namespace NonconvexAG.Smooth

/-- (2.13), p. 5 (outer ends of the chain). -/
theorem eq_2_13 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k →
      ‖g (xSeq g α β lam x0 (k - 1)) - g (xmdSeq g α β lam x0 k)‖ ≤
        LΨ * (1 - α k) * ‖xagSeq g α β lam x0 (k - 1) - xSeq g α β lam x0 (k - 1)‖ := by sorry

end NonconvexAG.Smooth
