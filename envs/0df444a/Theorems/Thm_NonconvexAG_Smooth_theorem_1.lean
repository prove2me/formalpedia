-- Prove2me | Theorems.Thm_NonconvexAG_Smooth_theorem_1
-- name    : NonconvexAG.Smooth.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:44:10.364013+00:00
-- url     : https://prove2.me/theorems/789f0c84-3077-4b0b-9399-b3ed71c3e409
-- title:
--   Theorem 1 — AG on smooth Ψ: min‖∇Ψ(x^md_k)‖² ≤ (Ψ(x_0) − Ψ*)/Σλ_kC_k; for convex Ψ, Ψ(x^ag_N) − Ψ(x*) ≤ Γ_N‖x_0 − x*‖²/(2λ_1)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable, bounded from below, with $\|\nabla\Psi(y)-\nabla\Psi(x)\|\le L_\Psi\|y-x\|$ for all $x,y$, where $L_\Psi>0$, and let $\Psi^*=\inf_x\Psi(x)$. Let $\{x_k,x^{md}_k,x^{ag}_k\}$ be computed by Algorithm 1 from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k>0$, $\lambda_k>0$, and let $\Gamma_k$ be defined in (2.6). Fix $N\ge1$.
--
--   1. If $C_k>0$ for $k=1,\dots,N$, where
--   $$C_k=1-L_\Psi\lambda_k-\frac{L_\Psi(\lambda_k-\beta_k)^2}{2\alpha_k\Gamma_k\lambda_k}\Big(\sum_{\tau=k}^N\Gamma_\tau\Big)\qquad(2.7),$$
--   then
--   $$\min_{k=1,\dots,N}\|\nabla\Psi(x^{md}_k)\|^2\le\frac{\Psi(x_0)-\Psi^*}{\sum_{k=1}^N\lambda_kC_k}.\qquad(2.8)$$
--   2. Suppose moreover that $\Psi$ is convex and that $x^*$ is a minimizer of $\Psi$ on $\mathbb R^n$. If for $k=1,\dots,N$
--   $$\alpha_k\lambda_k\le\beta_k<\frac1{L_\Psi}\quad(2.9),\qquad \frac{\alpha_1}{\lambda_1\Gamma_1}\ge\frac{\alpha_2}{\lambda_2\Gamma_2}\ge\dots\ge\frac{\alpha_N}{\lambda_N\Gamma_N}\quad(2.10),$$
--   then
--   $$\min_{k=1,\dots,N}\|\nabla\Psi(x^{md}_k)\|^2\le\frac{\|x_0-x^*\|^2}{\lambda_1\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)},\qquad(2.11)$$
--   $$\Psi(x^{ag}_N)-\Psi(x^*)\le\frac{\Gamma_N\|x_0-x^*\|^2}{2\lambda_1}.\qquad(2.12)$$
--
--   Part 1 shows that the accelerated gradient method, with a suitable step-size policy, drives the gradient to zero on a nonconvex smooth problem at the rate of gradient descent; part 2 shows that the same method keeps the optimal $O(1/N^2)$ rate of Nesterov's method when $\Psi$ happens to be convex (for instance with $\alpha_k=2/(k+1)$, $\Gamma_N=2/(N(N+1))$).
--
--   **Formalization Note** The gradient is an explicit map `g` with `IsBetaSmooth Ψ g LΨ` (differentiability, gradient $=g$, and (1.2)). $L_\Psi>0$ as in (1.2). "Bounded from below" is the standing assumption of §2.1 (`BddBelow (Set.range Ψ)`), and $\Psi^*$ is the infimum `⨅ x, Ψ x`. The minimum over $k=1,\dots,N$ is `Finset.inf'` over `Finset.Icc 1 N`. $C_k$ depends on $N$. Conditions (2.7), (2.9) and (2.10) are imposed for $k=1,\dots,N$ only, the indices the proof uses. The two parts are the two conjuncts of the conclusion.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 5, Theorem 1 (with §1 (1.1)–(1.2), p. 1, and the standing assumption of §2.1, p. 4)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

namespace NonconvexAG.Smooth

/-- Theorem 1 (p. 5): a) and b). -/
theorem theorem_1 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n)
    (hbdd : BddBelow (Set.range Ψ)) (N : ℕ) (hN : 1 ≤ N) :
    -- a) under (2.7) for `k = 1, …, N`: (2.8)
    ((∀ k ∈ Finset.Icc 1 N, 0 < C LΨ α β lam N k) →
      (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN) (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) ≤
        (Ψ x0 - ⨅ x, Ψ x) / ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k) ∧
    -- b) `Ψ` convex with a minimizer `x*`, under (2.9) and (2.10) for `k = 1, …, N`: (2.11), (2.12)
    (∀ xstar : E n, ConvexOn ℝ Set.univ Ψ → (∀ x, Ψ xstar ≤ Ψ x) →
      (∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ β k < 1 / LΨ) →
      (∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
        α k / (lam k * Gamma α k) ≤ α (k - 1) / (lam (k - 1) * Gamma α (k - 1))) →
      (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN) (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) ≤
          ‖x0 - xstar‖ ^ 2 /
            (lam 1 * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) ∧
        Ψ (xagSeq g α β lam x0 N) - Ψ xstar ≤ Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)) := by sorry

end NonconvexAG.Smooth
