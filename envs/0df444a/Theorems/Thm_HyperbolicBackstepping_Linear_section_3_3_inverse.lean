-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Linear_section_3_3_inverse
-- name    : HyperbolicBackstepping.Linear.section_3_3_inverse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:55.07524+00:00
-- url     : https://prove2.me/theorems/c0cb4fb3-2541-47ea-b935-91cdf6757476
-- title:
--   §3.3, p. 6 — a solution of the inverse kernel equations (3.40)–(3.47) maps the target equation back to the plant via (3.38)
-- statement:
--   Let $\epsilon_1,\epsilon_2$ be $C^1$ and positive on $[0,1]$, let $c_1,c_2$ be continuous, and let $q\neq0$. Let $L=\begin{pmatrix}L^{\alpha\alpha}&L^{\alpha\beta}\\L^{\beta\alpha}&L^{\beta\beta}\end{pmatrix}$ be a $C^1$ solution of the inverse kernel equations (3.40)–(3.43) on $\mathcal T=\{0\le\xi\le x\le1\}$ with boundary conditions (3.44)–(3.47). Let $\gamma=[\alpha\ \beta]^T$ be a classical solution of
--   $$\gamma_t=\Sigma(x)\gamma_x\quad(x\in[0,1],\ t\ge0),\qquad \alpha(0,t)=q\beta(0,t).$$
--   Then
--   $$w(x,t)=\gamma(x,t)+\int_0^xL(x,\xi)\gamma(\xi,t)\,d\xi$$
--   is a classical solution of $w_t=\Sigma(x)w_x+C(x)w$ on $[0,1]\times[0,\infty)$ with $u(0,t)=qv(0,t)$.
--
--   Together with §3.2 this is how the paper passes from the explicit solution of the target system back to the original state.
--
--   **Formalization Note** No right boundary condition is asserted for $w$: its value at $x=1$ is whatever $\gamma(1,t)$ produces, and the paper asserts nothing more. Solutions are classical ($C^1$ on $\mathbb R^2$).
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 6, §3.3, (3.38)–(3.47)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Linear_Basic

namespace HyperbolicBackstepping.Linear

open Set

/-- §3.3, p. 6: if `L` solves the inverse kernel equations (3.40)–(3.47) and `γ` is a classical
solution of (3.4) with `α(0, t) = q β(0, t)`, then `w = γ + ∫₀ˣ L(x, ξ) γ(ξ, t) dξ` (3.38) is a
classical solution of (3.1) with `u(0, t) = q v(0, t)`. -/
theorem section_3_3_inverse (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ)
    (hε₁ : ContDiff ℝ 1 ε₁) (hε₂ : ContDiff ℝ 1 ε₂)
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 < ε₁ x ∧ 0 < ε₂ x) (hq : q ≠ 0)
    (Laa Lab Lba Lbb : ℝ → ℝ → ℝ) (hL : IsInvKernel ε₁ ε₂ c₁ c₂ q Laa Lab Lba Lbb)
    (γ : ℝ → ℝ → Fin 2 → ℝ) (hγ : IsTargetPDESolution ε₁ ε₂ q γ) :
    IsPlantSolution ε₁ ε₂ c₁ c₂ q (Ltrans Laa Lab Lba Lbb γ) := by sorry

end HyperbolicBackstepping.Linear
