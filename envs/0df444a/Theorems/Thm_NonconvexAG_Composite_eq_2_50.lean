-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_50
-- name    : NonconvexAG.Composite.eq_2_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:36:17.124146+00:00
-- url     : https://prove2.me/theorems/9e9b0519-d07e-420f-a253-b3e5df29fc0d
-- title:
--   (2.50) — the combined prox inequality under α_kλ_k ≤ β_k
-- statement:
--   In the setting of (2.48)–(2.49) ($\mathcal X$ convex on its domain $K$, $\mathcal P$ a prox map, Algorithm 2 with $\alpha_1=1$, $\alpha_k\in(0,1)$ for $k\ge2$, $\beta_k,\lambda_k>0$), let $k\ge1$ satisfy $\alpha_k\lambda_k\le\beta_k$. Then for every $x\in K$
--   $$\big\langle\nabla\Psi(x^{md}_k),\,x^{ag}_k-\alpha_kx-(1-\alpha_k)x^{ag}_{k-1}\big\rangle+\mathcal X(x^{ag}_k)\le(1-\alpha_k)\mathcal X(x^{ag}_{k-1})+\alpha_k\mathcal X(x)+\frac{\alpha_k}{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2\Big]-\frac1{2\beta_k}\|x^{ag}_k-x^{md}_k\|^2 .$$
--
--   It combines the two prox inequalities with the convexity of $\mathcal X$; the condition $\alpha_k\lambda_k\le\beta_k$ (the first half of (2.9)) removes the term in $\|x_k-x_{k-1}\|^2$.
--
--   **Formalization Note** Only the outer ends of the printed chain are stated. At $k=1$ the term $(1-\alpha_1)\mathcal X(x^{ag}_0)$ vanishes because $\alpha_1=1$, so no assumption $x_0\in K$ is made.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 12, (2.50)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.50), p. 12 (outer ends of the chain), for every `k ≥ 1` with `αₖλₖ ≤ βₖ` and every `x` in
the domain `K` of `𝒳`. -/
theorem eq_2_50 {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n) :
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ k, 1 ≤ k → α k * lam k ≤ β k → ∀ x ∈ K,
      inner ℝ (gΨ (xmd k)) (xag k - α k • x - (1 - α k) • xag (k - 1)) + X (xag k) ≤
        (1 - α k) * X (xag (k - 1)) + α k * X x +
          α k / (2 * lam k) * (‖xk (k - 1) - x‖ ^ 2 - ‖xk k - x‖ ^ 2) -
          1 / (2 * β k) * ‖xag k - xmd k‖ ^ 2 := by sorry
end NonconvexAG.Composite
