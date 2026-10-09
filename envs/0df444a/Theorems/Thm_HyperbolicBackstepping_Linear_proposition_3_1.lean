-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Linear_proposition_3_1
-- name    : HyperbolicBackstepping.Linear.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:17.514329+00:00
-- url     : https://prove2.me/theorems/3f228bc2-b260-49f7-8058-658a30e939ca
-- title:
--   Proposition 3.1, p. 3 — the target system γ_t = Σγ_x decays at every exponential rate in L² and vanishes after t_F
-- statement:
--   Let $\epsilon_1,\epsilon_2$ be $C^1$ functions, positive on $[0,1]$, and let $q\in\mathbb R$ with $q\neq0$. Consider the target system
--   $$\alpha_t=-\epsilon_1(x)\alpha_x,\qquad \beta_t=\epsilon_2(x)\beta_x,\qquad \alpha(0,t)=q\beta(0,t),\qquad \beta(1,t)=0,$$
--   for $x\in[0,1]$, $t\ge0$, and write $\gamma=[\alpha\ \beta]^T$. Then:
--
--   1. for every $\lambda>0$ there is a constant $c>0$ such that every classical solution satisfies, for all $t\ge0$,
--   $$\|\gamma(\cdot,t)\|_{L^2}\le c\,e^{-\lambda t}\|\gamma(\cdot,0)\|_{L^2};$$
--   2. every classical solution vanishes identically on $[0,1]$ for every $t\ge t_F$, where
--   $$t_F=\int_0^1\left(\frac1{\epsilon_1(\xi)}+\frac1{\epsilon_2(\xi)}\right)d\xi.$$
--
--   The constant $c$ depends on $\lambda$, $\epsilon_1$, $\epsilon_2$ and $q$, but not on the solution. This is the behaviour of the target system to which the backstepping transformation maps the closed loop; Theorem 3.2 transfers it back to the original system.
--
--   **Formalization Note** The statement is restricted to classical solutions: $\gamma$ is jointly $C^1$ on $\mathbb R^2$ and $\gamma(\cdot,0)$ plays the role of the initial condition $\gamma_0\in L^2$. The hypothesis $q\neq0$ is the standing assumption of §§3.1–3.4.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 3, Proposition 3.1, (3.4)–(3.8)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Linear_Basic

namespace HyperbolicBackstepping.Linear

open Set

/-- Proposition 3.1 (p. 3), for classical solutions: every `C¹` solution of the target system
(3.4)–(3.5) satisfies `‖γ(·, t)‖_{L²} ≤ c e^{−λt} ‖γ(·, 0)‖_{L²}` for every `λ > 0`, with `c > 0`
depending only on `λ` and the data, and vanishes on `[0, 1]` for every `t ≥ t_F` (3.8).
The section assumes `q ≠ 0`. -/
theorem proposition_3_1 (ε₁ ε₂ : ℝ → ℝ) (q : ℝ)
    (hε₁ : ContDiff ℝ 1 ε₁) (hε₂ : ContDiff ℝ 1 ε₂)
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 < ε₁ x ∧ 0 < ε₂ x) (hq : q ≠ 0) :
    (∀ lam : ℝ, 0 < lam → ∃ c : ℝ, 0 < c ∧
      ∀ γ : ℝ → ℝ → Fin 2 → ℝ, IsTargetSolution ε₁ ε₂ q γ → ∀ t : ℝ, 0 ≤ t →
        L2norm (fun x => γ x t) ≤ c * Real.exp (-lam * t) * L2norm (fun x => γ x 0)) ∧
    (∀ γ : ℝ → ℝ → Fin 2 → ℝ, IsTargetSolution ε₁ ε₂ q γ →
      ∀ t : ℝ, tF ε₁ ε₂ ≤ t → ∀ x ∈ Icc (0:ℝ) 1, γ x t = 0) := by sorry

end HyperbolicBackstepping.Linear
