-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_53
-- name    : NonconvexAG.Composite.eq_2_53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:35.924251+00:00
-- url     : https://prove2.me/theorems/89db2b7d-ae75-4ab1-b740-a9f9ea96d903
-- title:
--   (2.53) — the summed bound at x* with the nonconvexity terms bounded by (L_f/Γ_N)(‖x*‖² + 2M²)
-- statement:
--   Consider problem (1.3) with $\Phi=\Psi+\mathcal X$ as in (2.51), Algorithm 2 with the prox map $\mathcal P$ of (2.37), Assumption 2 with constant $M$, and $\|x_0\|\le M$. Fix $N\ge1$ and suppose $\alpha_k\lambda_k\le\beta_k$ and (2.10) hold for $k=1,\dots,N$. Then for every $x^*\in K$
--   $$\frac{\Phi(x^{ag}_N)-\Phi(x^*)}{\Gamma_N}+\sum_{k=1}^N\frac{1-L_\Psi\beta_k}{2\beta_k\Gamma_k}\|x^{ag}_k-x^{md}_k\|^2\le\frac{\|x_0-x^*\|^2}{2\lambda_1}+\frac{L_f}{\Gamma_N}\big(\|x^*\|^2+2M^2\big).$$
--
--   This is the summed inequality with $x=x^*$, (2.52) and (2.16); both conclusions of Theorem 2 are read off from it.
--
--   **Formalization Note** Only the outer ends of the printed chain are stated. The page prints $\|x_0-x\|^2$ on the right-hand side; since $x=x^*$ has been substituted, this is a typo for $\|x_0-x^*\|^2$, which is what is stated. The bound holds for every $x^*$ in the domain $K$; the paper applies it at an optimal solution. The added hypothesis $\|x_0\|\le M$ is explained under (2.52).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 13, (2.53)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.53), p. 13 (outer ends of the chain, with `‖x₀ − x*‖²` for the printed `‖x₀ − x‖²`): under
Assumption 2 and `‖x₀‖ ≤ M`, for every `N ≥ 1` and every point `x*` of the domain `K` of `𝒳`, when
`αₖλₖ ≤ βₖ` (first half of (2.9)) and (2.10) hold for `k = 1, …, N`. -/
theorem eq_2_53 {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) :
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ xstar ∈ K,
      (Φ (xag N) - Φ xstar) / NonconvexAG.Smooth.Gamma α N +
          ∑ k ∈ Finset.Icc 1 N,
            (1 - (Lf + Lh) * β k) / (2 * β k * NonconvexAG.Smooth.Gamma α k) * ‖xag k - xmd k‖ ^ 2 ≤
        ‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by sorry
end NonconvexAG.Composite
