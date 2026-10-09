-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_51
-- name    : NonconvexAG.Composite.eq_2_51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:58.331495+00:00
-- url     : https://prove2.me/theorems/5c54767a-a908-4bb2-b8e5-504ccfdd64c2
-- title:
--   (2.51) — the one-step inequality for Φ = Ψ + 𝒳 along Algorithm 2
-- statement:
--   Consider problem (1.3): $\Psi=f+h$ with $f$ $L_f$-smooth, $h$ convex and $L_h$-smooth, $L_\Psi=L_f+L_h$, and $\mathcal X$ convex on its domain $K$; let $\Phi=\Psi+\mathcal X$. Run Algorithm 2 with the prox map $\mathcal P$ of (2.37) and step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$. For every $k\ge1$ with $\alpha_k\lambda_k\le\beta_k$ and every $x\in K$,
--   $$\Phi(x^{ag}_k)\le(1-\alpha_k)\Phi(x^{ag}_{k-1})+\alpha_k\Phi(x)-\frac12\Big(\frac1{\beta_k}-L_\Psi\Big)\|x^{ag}_k-x^{md}_k\|^2+\frac{\alpha_k}{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2\Big]+\frac{L_f\alpha_k}2\|x^{md}_k-x\|^2+\frac{L_f\alpha_k^2(1-\alpha_k)}2\|x^{ag}_{k-1}-x_{k-1}\|^2 .$$
--
--   It is the one-step progress inequality of the method, obtained by adding the descent bound (2.46), the lower bound (2.47) and the prox bound (2.50).
--
--   **Formalization Note** $\mathcal X$ is the pair `(K, X)` and $x$ ranges over $K$. At $k=1$ the terms in $x^{ag}_0=x_0$ carry the factor $1-\alpha_1=0$, so $x_0\in K$ is not assumed.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 12, (2.51)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.51), p. 12, for Algorithm 2 on `Φ = f + h + 𝒳`, every `k ≥ 1` with `αₖλₖ ≤ βₖ` and
every `x` in the domain `K` of `𝒳`; `L_Ψ = L_f + L_h`. -/
theorem eq_2_51 {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n) :
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ k, 1 ≤ k → α k * lam k ≤ β k → ∀ x ∈ K,
      Φ (xag k) ≤ (1 - α k) * Φ (xag (k - 1)) + α k * Φ x -
          1 / 2 * (1 / β k - (Lf + Lh)) * ‖xag k - xmd k‖ ^ 2 +
          α k / (2 * lam k) * (‖xk (k - 1) - x‖ ^ 2 - ‖xk k - x‖ ^ 2) +
          Lf * α k / 2 * ‖xmd k - x‖ ^ 2 +
          Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) - xk (k - 1)‖ ^ 2 := by sorry
end NonconvexAG.Composite
