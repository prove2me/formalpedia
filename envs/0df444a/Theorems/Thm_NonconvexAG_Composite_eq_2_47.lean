-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_47
-- name    : NonconvexAG.Composite.eq_2_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:19.217454+00:00
-- url     : https://prove2.me/theorems/dfa94003-b907-4d7a-83e4-024328d7fd60
-- title:
--   (2.47) — the L_f-corrected convexity gap at x^md_k
-- statement:
--   Let $\Psi=f+h$ be as in (1.3) and Lemma 5 ($f$ $L_f$-smooth, $h$ convex and $L_h$-smooth, $\nabla\Psi=\nabla f+\nabla h$), and run Algorithm 2 with step sizes satisfying $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, any prox map and any starting point $x_0$. Then for every $k\ge1$ and every $x\in\mathbb R^n$,
--   $$\Psi(x^{md}_k)-\big[(1-\alpha_k)\Psi(x^{ag}_{k-1})+\alpha_k\Psi(x)\big]\le\big\langle\nabla\Psi(x^{md}_k),\,x^{md}_k-\alpha_kx-(1-\alpha_k)x^{ag}_{k-1}\big\rangle+\frac{L_f\alpha_k}2\|x^{md}_k-x\|^2+\frac{L_f\alpha_k^2(1-\alpha_k)}2\|x^{ag}_{k-1}-x_{k-1}\|^2 .$$
--
--   For convex $\Psi$ (the case $L_f=0$) this is the familiar convexity step of accelerated methods; the two $L_f$-terms measure the price of nonconvexity of $f$.
--
--   **Formalization Note** Only the outer ends of the printed chain are stated. The prox map plays no role here beyond defining the iterates.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 12, (2.47)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.47), p. 12 (outer ends of the chain), for Algorithm 2 on `Ψ = f + h`, every `k ≥ 1` and
every `x ∈ ℝⁿ`. -/
theorem eq_2_47 {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n) :
    let Ψ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ k, 1 ≤ k → ∀ x : NonconvexAG.Smooth.E n,
      Ψ (xmd k) - ((1 - α k) * Ψ (xag (k - 1)) + α k * Ψ x) ≤
        inner ℝ (gΨ (xmd k)) (xmd k - α k • x - (1 - α k) • xag (k - 1)) +
          Lf * α k / 2 * ‖xmd k - x‖ ^ 2 +
          Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) - xk (k - 1)‖ ^ 2 := by sorry
end NonconvexAG.Composite
