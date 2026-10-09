-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Linear_section_3_2_mapping
-- name    : HyperbolicBackstepping.Linear.section_3_2_mapping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:45.003492+00:00
-- url     : https://prove2.me/theorems/eac01466-56b8-4869-884d-04819913e85b
-- title:
--   §3.2, p. 5 — a solution of the kernel equations (3.30)–(3.37) maps the closed loop into the target system via (3.23)
-- statement:
--   Let $\epsilon_1,\epsilon_2$ be $C^1$ and positive on $[0,1]$, let $c_1,c_2$ be continuous, and let $q\neq0$. Let $K=\begin{pmatrix}K^{uu}&K^{uv}\\K^{vu}&K^{vv}\end{pmatrix}$ be a $C^1$ solution of the kernel equations (3.30)–(3.33) on the triangle $\mathcal T=\{0\le\xi\le x\le1\}$ with boundary conditions (3.34)–(3.37). Let $w=[u\ v]^T$ be a classical solution of the closed loop
--   $$w_t=\Sigma(x)w_x+C(x)w,\qquad u(0,t)=qv(0,t),\qquad v(1,t)=\int_0^1K^{vu}(1,\xi)u(\xi,t)\,d\xi+\int_0^1K^{vv}(1,\xi)v(\xi,t)\,d\xi .$$
--   Then
--   $$\gamma(x,t)=w(x,t)-\int_0^xK(x,\xi)w(\xi,t)\,d\xi$$
--   is a classical solution of the target system $\gamma_t=\Sigma(x)\gamma_x$, $\alpha(0,t)=q\beta(0,t)$, $\beta(1,t)=0$.
--
--   The paper derives (3.30)–(3.37) by expanding the matrix conditions (3.27)–(3.29),
--   $0=C(x)+\Sigma(x)K(x,x)-K(x,x)\Sigma(x)$, $0=\Sigma(x)K_x+K_\xi\Sigma(\xi)+K\Sigma'(\xi)-KC(\xi)$, $0=K(x,0)\Sigma(0)Q_0$ with $Q_0=\begin{pmatrix}0&q\\0&1\end{pmatrix}$. This is the step that converts the stabilization problem for the plant into the known behaviour of the target system.
--
--   **Formalization Note** Only the "if" direction of the paper's "if and only if" is stated, in the expanded form (3.30)–(3.37) the paper solves; the "only if" direction depends on what "mapped into" means and is not formalized. Solutions are classical ($C^1$); the right boundary condition is the feedback (3.48) evaluated on the same state.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 5, §3.2, sentence after (3.26), with (3.23), (3.27)–(3.37), (3.48)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Linear_Basic

namespace HyperbolicBackstepping.Linear

open Set

/-- §3.2, p. 5 (the "if" direction of the claim after (3.26), in the expanded form (3.30)–(3.37)):
if `K` solves the kernel equations (3.30)–(3.37) and `w` is a classical solution of the closed
loop (3.1), (3.3), (3.48), then `γ = w − ∫₀ˣ K(x, ξ) w(ξ, t) dξ` (3.23) is a classical solution
of the target system (3.4)–(3.5). -/
theorem section_3_2_mapping (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ)
    (hε₁ : ContDiff ℝ 1 ε₁) (hε₂ : ContDiff ℝ 1 ε₂)
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 < ε₁ x ∧ 0 < ε₂ x) (hq : q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ) (hK : IsKernel ε₁ ε₂ c₁ c₂ q Kuu Kuv Kvu Kvv)
    (w : ℝ → ℝ → Fin 2 → ℝ) (hw : IsClosedLoopSolution ε₁ ε₂ c₁ c₂ q Kvu Kvv w) :
    IsTargetSolution ε₁ ε₂ q (Ktrans Kuu Kuv Kvu Kvv w) := by sorry

end HyperbolicBackstepping.Linear
