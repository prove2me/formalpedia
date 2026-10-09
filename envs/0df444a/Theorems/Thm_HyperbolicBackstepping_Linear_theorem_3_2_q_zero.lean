-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Linear_theorem_3_2_q_zero
-- name    : HyperbolicBackstepping.Linear.theorem_3_2_q_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:30.865012+00:00
-- url     : https://prove2.me/theorems/72614ef6-7679-4c90-b060-06975155f29e
-- title:
--   §3.5, p. 8 — for q = 0 the feedback (3.48) gives the same result as Theorem 3.2
-- statement:
--   Let $\epsilon_1,\epsilon_2$ be $C^1$ and positive on $[0,1]$ and let $c_1,c_2$ be continuous. Take $q=0$ in the boundary condition $u(0,t)=qv(0,t)$, so $u(0,t)=0$. Let $K^{vu},K^{vv}$ be $C^1$ solutions on $\mathcal T$ of (3.32), (3.33) with (3.36) and (3.37), where (3.37) now reads $K^{vv}(x,0)=0$. Consider classical solutions $w=[u\ v]^T$ of the closed loop
--   $$w_t=\Sigma(x)w_x+C(x)w,\qquad u(0,t)=0,\qquad v(1,t)=\int_0^1K^{vu}(1,\xi)u(\xi,t)\,d\xi+\int_0^1K^{vv}(1,\xi)v(\xi,t)\,d\xi .$$
--   Then:
--
--   1. for every $\lambda>0$ there is $c>0$ such that every such solution satisfies, for all $t\ge0$,
--   $$\|w(\cdot,t)\|_{L^2}\le c\,e^{-\lambda t}\|w(\cdot,0)\|_{L^2};$$
--   2. every such solution vanishes on $[0,1]$ for every $t\ge t_F=\int_0^1\left(\frac1{\epsilon_1}+\frac1{\epsilon_2}\right)d\xi$.
--
--   The paper treats $q=0$ separately because its kernel condition (3.34) divides by $q$; the feedback law only uses $K^{vu},K^{vv}$, which remain uniquely defined.
--
--   **Formalization Note** Restricted to classical ($C^1$) solutions, with $w(\cdot,0)$ as initial condition. The constant $c$ is quantified before the solution, so it depends only on $\lambda$ and the data.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, pp. 7–8, §3.5, with Theorem 3.2 (p. 6)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Linear_Basic

namespace HyperbolicBackstepping.Linear

open Set

/-- §3.5, p. 8 (the case `q = 0`), for classical solutions: with `q = 0` in (3.3) and the
kernels `K^{vu}, K^{vv}` of (3.32), (3.33), (3.36), (3.37) (where (3.37) reads `K^{vv}(x, 0) = 0`),
the conclusion of Theorem 3.2 holds: the `L²` estimate (3.49) for every `λ > 0`, with `c` uniform
over solutions, and `w ≡ 0` on `[0, 1]` for every `t ≥ t_F`. -/
theorem theorem_3_2_q_zero (ε₁ ε₂ c₁ c₂ : ℝ → ℝ)
    (hε₁ : ContDiff ℝ 1 ε₁) (hε₂ : ContDiff ℝ 1 ε₂)
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 < ε₁ x ∧ 0 < ε₂ x)
    (Kvu Kvv : ℝ → ℝ → ℝ) (hK : IsVKernel ε₁ ε₂ c₁ c₂ 0 Kvu Kvv) :
    (∀ lam : ℝ, 0 < lam → ∃ c : ℝ, 0 < c ∧
      ∀ w : ℝ → ℝ → Fin 2 → ℝ, IsClosedLoopSolution ε₁ ε₂ c₁ c₂ 0 Kvu Kvv w →
        ∀ t : ℝ, 0 ≤ t →
          L2norm (fun x => w x t) ≤ c * Real.exp (-lam * t) * L2norm (fun x => w x 0)) ∧
    (∀ w : ℝ → ℝ → Fin 2 → ℝ, IsClosedLoopSolution ε₁ ε₂ c₁ c₂ 0 Kvu Kvv w →
      ∀ t : ℝ, tF ε₁ ε₂ ≤ t → ∀ x ∈ Icc (0:ℝ) 1, w x t = 0) := by sorry

end HyperbolicBackstepping.Linear
