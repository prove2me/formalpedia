-- Prove2me | Theorems.Thm_NonconvexDRS_Tight_theorem_4_8
-- name    : NonconvexDRS.Tight.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:55.377433+00:00
-- url     : https://prove2.me/theorems/3451e994-a927-418f-a0da-fc660de9d91e
-- title:
--   Theorem 4.8, pp. 16–17 — over-relaxation λ > 2(1+γσ) defeats DRS even with strongly convex φ₂, unless s⁰ is a fixed point
-- statement:
--   **Theorem 4.8 (Necessity of $0<\lambda<2(1+\gamma\sigma)$).** Let $p\ge0$, $L>0$ and $\sigma\in[-L,L]$. There exist $\varphi_1:\mathbb R^p\to\mathbb R$ and $\varphi_2:\mathbb R^p\to\overline{\mathbb R}$ such that
--
--   1. $\varphi_1$ is $L$-smooth and $\sigma$-hypoconvex;
--   2. $\varphi_2$ is proper, lower semicontinuous and strongly convex;
--   3. $\operatorname{arg\,min}(\varphi_1+\varphi_2)\neq\emptyset$;
--   4. for every $0<\gamma<1/L$, every $\lambda>2(1+\gamma\sigma)$ and every DRS run $(s^k,u^k,v^k)_{k\in\mathbb N}$ with stepsize $\gamma$ and relaxation $\lambda$, either $s^0$ is a fixed point of the DR-iteration, or
--   $$\|s^k-s^{k+1}\|\not\to0\qquad\text{as }k\to\infty.$$
--
--   So even when $\varphi_2$ is strongly convex, the relaxation bound $\lambda<2(1+\gamma\sigma)$ of the paper's convergence theorem cannot be dropped.
--
--   **Formalization Note** The statement is the printed one. The paper's own construction ((4.12) with $t=1$, $\varphi_2=\delta_{\{p\}}$) does not prove it: with $L=1$, $\sigma=-1$, $\gamma=\tfrac12$, $\lambda=\tfrac65$, $p=2$ and $s^0=-2$, one step gives $s^1=2$, a fixed point, while $s^0$ is not one. The claim is existential, though, and other choices of $\varphi_1,\varphi_2$ may be used. Every dimension $p\ge0$ is covered (on $\mathbb R^0$ every point is a fixed point). The bound $\gamma<1/L$ is written $\gamma L<1$. Strong convexity of an extended-real function means that, for some $\mu>0$, $\operatorname{dom}\varphi_2$ is convex and $\varphi_2-\tfrac\mu2\|\cdot\|^2$ is convex on it.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 16–17, Theorem 4.8

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace NonconvexDRS.Tight

theorem theorem_4_8 (p : ℕ) (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) :
    ∃ (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal),
      (IsLSmooth φ₁ L ∧ IsHypoconvex φ₁ σ) ∧
      (IsProper φ₂ ∧ LowerSemicontinuous φ₂ ∧ IsStronglyConvexE φ₂) ∧
      (∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x) ∧
      ∀ (γ lam : ℝ), 0 < γ → γ * L < 1 → 2 * (1 + γ * σ) < lam →
        ∀ s u v : ℕ → EuclideanSpace ℝ (Fin p), IsDRSRun φ₁ φ₂ γ lam s u v →
          IsDRSFixedPoint φ₁ φ₂ γ (s 0) ∨
            ¬ Tendsto (fun k => ‖s k - s (k + 1)‖) atTop (𝓝 0) := by sorry

end NonconvexDRS.Tight
