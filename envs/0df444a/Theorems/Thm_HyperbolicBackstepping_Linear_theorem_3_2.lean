-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Linear_theorem_3_2
-- name    : HyperbolicBackstepping.Linear.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:26.186259+00:00
-- url     : https://prove2.me/theorems/bb05aed2-105f-4bbe-9747-df78da6182ac
-- title:
--   Theorem 3.2, pp. 6–7 — the backstepping feedback (3.48) makes the linear 2 × 2 hyperbolic system decay at every exponential rate and vanish after t_F
-- statement:
--   Let $\epsilon_1,\epsilon_2$ be $C^1$ functions, positive on $[0,1]$, let $c_1,c_2$ be continuous, and let $q\neq0$. Consider the system
--   $$w_t=\Sigma(x)w_x+C(x)w,\qquad \Sigma=\begin{pmatrix}-\epsilon_1&0\\0&\epsilon_2\end{pmatrix},\quad C=\begin{pmatrix}0&c_1\\c_2&0\end{pmatrix},$$
--   for $w=[u\ v]^T$, $x\in[0,1]$, $t\ge0$, with $u(0,t)=qv(0,t)$ and the boundary feedback
--   $$v(1,t)=\int_0^1K^{vu}(1,\xi)u(\xi,t)\,d\xi+\int_0^1K^{vv}(1,\xi)v(\xi,t)\,d\xi,$$
--   where $K^{vu},K^{vv}$ are $C^1$ solutions on $\mathcal T=\{0\le\xi\le x\le1\}$ of the kernel equations (3.32), (3.33) with (3.36), (3.37). Then:
--
--   1. for every $\lambda>0$ there is $c>0$ such that every classical closed-loop solution satisfies, for all $t\ge0$,
--   $$\|w(\cdot,t)\|_{L^2}\le c\,e^{-\lambda t}\|w(\cdot,0)\|_{L^2};$$
--   2. every classical closed-loop solution vanishes identically on $[0,1]$ for every $t\ge t_F$, where
--   $$t_F=\int_0^1\left(\frac1{\epsilon_1(\xi)}+\frac1{\epsilon_2(\xi)}\right)d\xi .$$
--
--   This is the linear backstepping result of the paper: a full-state boundary feedback, computed once from the coefficients, drives every state of the linear $2\times2$ hyperbolic system to zero in the minimal time $t_F$; the paper's main theorem applies the same feedback to the quasilinear system.
--
--   **Formalization Note** The statement is restricted to classical solutions: $w$ is jointly $C^1$ on $\mathbb R^2$, the equations hold on $[0,1]\times[0,\infty)$, and $w(\cdot,0)$ is the initial condition $w_0\in L^2$. The constant $c$ is quantified before the solution, so it depends only on $\lambda$ and the data. Only $K^{vu},K^{vv}$ enter the feedback and they solve a closed subsystem of (3.30)–(3.37), so they are the hypothesis; by Theorem A.1 that subsystem has a unique solution. A $C^1$ kernel is guaranteed when $c_1,c_2$ are $C^1$ (Theorem A.2); for merely continuous $c_i$ without a $C^1$ kernel the statement is vacuous for that data, never false. The hypothesis $q\neq0$ is the standing assumption of §§3.1–3.4 ("thus assuming $q\neq0$", p. 3); the case $q=0$ is the separate statement of §3.5.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, pp. 6–7, Theorem 3.2, with (3.1)–(3.3), (3.8), (3.32)–(3.37), (3.48)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Linear_Basic

namespace HyperbolicBackstepping.Linear

open Set

/-- Theorem 3.2 (pp. 6–7), for classical solutions and `q ≠ 0`: with the feedback (3.48) built
from the kernels `K^{vu}, K^{vv}` of (3.32), (3.33), (3.36), (3.37), every `C¹` solution of the
closed loop satisfies `‖w(·, t)‖_{L²} ≤ c e^{−λt} ‖w(·, 0)‖_{L²}` (3.49) for every `λ > 0`, with
`c > 0` uniform over solutions, and `w ≡ 0` on `[0, 1]` for every `t ≥ t_F` (3.8). -/
theorem theorem_3_2 (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ)
    (hε₁ : ContDiff ℝ 1 ε₁) (hε₂ : ContDiff ℝ 1 ε₂)
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 < ε₁ x ∧ 0 < ε₂ x) (hq : q ≠ 0)
    (Kvu Kvv : ℝ → ℝ → ℝ) (hK : IsVKernel ε₁ ε₂ c₁ c₂ q Kvu Kvv) :
    (∀ lam : ℝ, 0 < lam → ∃ c : ℝ, 0 < c ∧
      ∀ w : ℝ → ℝ → Fin 2 → ℝ, IsClosedLoopSolution ε₁ ε₂ c₁ c₂ q Kvu Kvv w →
        ∀ t : ℝ, 0 ≤ t →
          L2norm (fun x => w x t) ≤ c * Real.exp (-lam * t) * L2norm (fun x => w x 0)) ∧
    (∀ w : ℝ → ℝ → Fin 2 → ℝ, IsClosedLoopSolution ε₁ ε₂ c₁ c₂ q Kvu Kvv w →
      ∀ t : ℝ, tF ε₁ ε₂ ≤ t → ∀ x ∈ Icc (0:ℝ) 1, w x t = 0) := by sorry

end HyperbolicBackstepping.Linear
