-- Prove2me | Theorems.Thm_NonconvexAG_Composite_theorem_2
-- name    : NonconvexAG.Composite.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:36:38.628302+00:00
-- url     : https://prove2.me/theorems/5ae4f25d-9be8-4b4b-a544-f3aad45502ce
-- title:
--   Theorem 2 — the AG method drives the gradient mapping to zero on nonconvex composite problems, at the optimal rate when L_f = 0
-- statement:
--   Consider the composite problem (1.3),
--   $$\min_{x\in\mathbb R^n}\ \Phi(x):=\Psi(x)+\mathcal X(x),\qquad\Psi=f+h,$$
--   where $f$ is differentiable with $L_f$-Lipschitz gradient and possibly nonconvex, $h$ is convex and differentiable with $L_h$-Lipschitz gradient, $L_\Psi=L_f+L_h$, and $\mathcal X$ is convex with domain $K$. Let $\mathcal P$ be the prox map (2.37) and $\mathcal G$ the gradient mapping (2.38), and suppose Assumption 2 holds: $\|\mathcal P(x,y,c)\|\le M$ for all $x,y$ and $c>0$. Run Algorithm 2 from $x_0$ with $\|x_0\|\le M$ and step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, and let $\Gamma_k$ be given by (2.6). Fix $N\ge1$ and suppose that for $k=1,\dots,N$
--   $$\alpha_k\lambda_k\le\beta_k<\frac1{L_\Psi}\quad(2.9),\qquad\frac{\alpha_1}{\lambda_1\Gamma_1}\ge\frac{\alpha_2}{\lambda_2\Gamma_2}\ge\dots\ge\frac{\alpha_N}{\lambda_N\Gamma_N}\quad(2.10).$$
--   Let $x^*\in K$ be an optimal solution of (1.3). Then
--   $$\min_{k=1,\dots,N}\big\|\mathcal G\big(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k\big)\big\|^2\le2\Big[\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)\Big]^{-1}\Big[\frac{\|x_0-x^*\|^2}{2\lambda_1}+\frac{L_f}{\Gamma_N}\big(\|x^*\|^2+2M^2\big)\Big],\qquad(2.44)$$
--   and if, in addition, $L_f=0$, then
--   $$\Phi(x^{ag}_N)-\Phi(x^*)\le\frac{\Gamma_N\|x_0-x^*\|^2}{2\lambda_1}.\qquad(2.45)$$
--
--   The same aggressive step-size policy that is optimal for convex problems thus yields a convergence guarantee for the gradient mapping when $f$ is nonconvex, and recovers the optimal convex rate for the optimality gap when $f$ is affine.
--
--   **Formalization Note** $\mathcal X$ is the pair `(K, X)`: its domain `K` and its finite values on `K`; $\Phi$ is compared only on `K`, and the optimality of $x^*$ is $\Phi(x^*)\le\Phi(u)$ for all $u\in K$. The prox map is an explicit function `P` with the minimizer property `IsProxMap K X P`. The second half of (2.9) is written $L_\Psi\beta_k<1$, which equals $\beta_k<1/L_\Psi$ when $L_\Psi>0$ and reads $1/0=+\infty$ when $L_\Psi=0$. The minimum is `Finset.inf'` over $\{1,\dots,N\}$. **Added hypothesis** $\|x_0\|\le M$: the proof uses $\|x_0\|=\|x^{ag}_0\|\le M$ in (2.52) at $k=1$, which Assumption 2 does not provide because $x_0$ is the input rather than a prox output; it holds whenever $x_0\in\operatorname{dom}\mathcal X$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 11, Theorem 2 (2.44)–(2.45); conditions (2.9)–(2.10), p. 5; problem (1.3), p. 2

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- Theorem 2 (p. 11): (2.44), and (2.45) when `L_f = 0`. The problem is (1.3): `Ψ = f + h` with
`f ∈ C^{1,1}_{L_f}`, `h ∈ C^{1,1}_{L_h}` convex, `L_Ψ = L_f + L_h`, and `𝒳` convex with domain `K`;
`Φ = Ψ + 𝒳`. Algorithm 2 runs with the prox map `P` of (2.37), under Assumption 2 and `‖x₀‖ ≤ M`,
with (2.9) (`αₖλₖ ≤ βₖ` and `L_Ψ βₖ < 1`, i.e. `βₖ < 1/L_Ψ`) and (2.10) for `k = 1, …, N`, and `x*` an
optimal solution of (1.3). -/
theorem theorem_2 {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    (N : ℕ) (hN : 1 ≤ N)
    (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ (Lf + Lh) * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (xstar : NonconvexAG.Smooth.E n) (hxstar : xstar ∈ K)
    (hopt : ∀ u ∈ K, f xstar + h xstar + X xstar ≤ f u + h u + X u) :
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    -- (2.44)
    (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
        (fun k => ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2) ≤
      2 * (∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - (Lf + Lh) * β k))⁻¹ *
        (‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2)) ∧
    -- (2.45)
    (Lf = 0 → Φ (xag N) - Φ xstar ≤ NonconvexAG.Smooth.Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)) := by sorry
end NonconvexAG.Composite
