-- Prove2me | Theorems.Thm_GhadimiLan2016_theorem_2_faithful
-- name    : GhadimiLan2016.theorem_2_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T00:55:46.015063+00:00
-- url     : https://prove2.me/theorems/195079bb-adf6-422a-8fef-30435f022a9c
-- title:
--   Theorem 2 (Ghadimi–Lan), as stated in the paper: any starting point x₀
-- statement:
--   Let $\Psi=f+h$ on $\mathbb R^n$, where $f$ has an $L_f$-Lipschitz gradient (possibly nonconvex) and $h$ is convex with an $L_h$-Lipschitz gradient; write $L_\Psi=L_f+L_h$. Let $\mathcal X$ be a convex function with domain $K$, let $\Phi=\Psi+\mathcal X$, and let $\mathcal P(x,y,c)=\operatorname{argmin}_{u\in K}\{\langle y,u\rangle+\frac{1}{2c}\|u-x\|^2+\mathcal X(u)\}$ be its prox map, with gradient mapping $\mathcal G(x,y,c)=\frac1c[x-\mathcal P(x,y,c)]$. Assume (Assumption 2) $\|\mathcal P(x,y,c)\|\le M$ for all $x,y$ and $c>0$, and let $x^*\in K$ minimize $\Phi$. Run Algorithm 2 (the accelerated gradient method with prox steps $x_k=\mathcal P(x_{k-1},\nabla\Psi(x^{md}_k),\lambda_k)$, $x^{ag}_k=\mathcal P(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k)$, $x^{md}_k=(1-\alpha_k)x^{ag}_{k-1}+\alpha_kx_{k-1}$, $x^{ag}_0=x_0$) from an arbitrary $x_0\in\mathbb R^n$, with $\alpha_1=1$, $\alpha_k\in(0,1)$ for $k\ge2$, $\beta_k,\lambda_k>0$, and for $k\le N$
--
--   $$\alpha_k\lambda_k\le\beta_k,\qquad L_\Psi\beta_k<1,\qquad \frac{\alpha_k}{\lambda_k\Gamma_k}\le\frac{\alpha_{k-1}}{\lambda_{k-1}\Gamma_{k-1}},$$
--
--   where $\Gamma_k=\prod_{i=2}^k(1-\alpha_i)$. Then for every $N\ge1$:
--
--   1. $$\min_{1\le k\le N}\|\mathcal G(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k)\|^2\le 2\Big[\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)\Big]^{-1}\Big[\frac{\|x_0-x^*\|^2}{2\lambda_1}+\frac{L_f}{\Gamma_N}(\|x^*\|^2+2M^2)\Big];$$
--   2. if $L_f=0$, then $$\Phi(x^{ag}_N)-\Phi(x^*)\le\frac{\Gamma_N\|x_0-x^*\|^2}{2\lambda_1}.$$
--
--   This is Theorem 2 of Ghadimi and Lan, (2.44)–(2.45), as stated in the paper: the convergence guarantee of the accelerated gradient method on nonconvex composite problems. The existing platform formalization of Theorem 2 proves the same conclusions under the additional hypothesis $\|x_0\|\le M$, which the paper does not impose.
--
--   **Formalization Note** $\mathcal X$ is represented by the set $K$ and its finite values on $K$; the prox map is any map whose values lie in $K$ and minimize the prox objective over $K$. The step-size conditions are required only for $k\le N$, which is all the conclusion depends on.
-- source:
--   Ghadimi & Lan, Accelerated gradient methods for nonconvex nonlinear and stochastic programming, Math. Program. 156 (2016), arXiv:1310.3787, p. 11, Theorem 2, (2.44)–(2.45)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

open ConvexOptAlg.SmoothGD NonconvexAG.Composite

theorem GhadimiLan2016.theorem_2_faithful {n : ℕ} (f h : NonconvexAG.Smooth.E n → ℝ) (gf gh : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n)
    (M : ℝ) (hA2 : Assumption2 P M)
    (N : ℕ) (hN : 1 ≤ N)
    (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ (Lf + Lh) * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (xstar : NonconvexAG.Smooth.E n) (hxstar : xstar ∈ K)
    (hopt : ∀ u ∈ K, f xstar + h xstar + X xstar ≤ f u + h u + X u) :
    let Φ : NonconvexAG.Smooth.E n → ℝ := fun x => f x + h x + X x
    let gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n := fun x => gf x + gh x
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
        (fun k => ‖gradMap P (xmd k) (gΨ (xmd k)) (β k)‖ ^ 2) ≤
      2 * (∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - (Lf + Lh) * β k))⁻¹ *
        (‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2)) ∧
    (Lf = 0 → Φ (xag N) - Φ xstar ≤ NonconvexAG.Smooth.Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)) := by sorry
