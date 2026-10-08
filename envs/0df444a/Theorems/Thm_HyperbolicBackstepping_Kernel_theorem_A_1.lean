-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Kernel_theorem_A_1
-- name    : HyperbolicBackstepping.Kernel.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:36.207419+00:00
-- url     : https://prove2.me/theorems/8bdab8f1-7653-4c8e-b7bc-54d0cab2516c
-- title:
--   Theorem A.1, p. 19 — unique continuous solution of the four-component Goursat system
-- statement:
--   Consider the generalized Goursat problem (A.1)–(A.7) on the triangle $\mathcal T=\{(x,\xi):0\le\xi\le x\le1\}$:
--   $$\epsilon_1(x)F^1_x+\epsilon_1(\xi)F^1_\xi=g_1+\textstyle\sum_iC_{1i}F^i,\qquad \epsilon_1(x)F^2_x-\epsilon_2(\xi)F^2_\xi=g_2+\sum_iC_{2i}F^i,$$
--   $$\epsilon_2(x)F^3_x-\epsilon_1(\xi)F^3_\xi=g_3+\textstyle\sum_iC_{3i}F^i,\qquad \epsilon_2(x)F^4_x+\epsilon_2(\xi)F^4_\xi=g_4+\sum_iC_{4i}F^i,$$
--   with $F^1(x,0)=h_1(x)+q_1(x)F^2(x,0)+q_2(x)F^3(x,0)$, $F^2(x,x)=h_2(x)$, $F^3(x,x)=h_3(x)$ and $F^4(x,0)=h_4(x)+q_3(x)F^2(x,0)+q_4(x)F^3(x,0)$.
--
--   Assume $q_i,h_i\in C([0,1])$, $g_i,C_{ji}\in C(\mathcal T)$ ($i,j=1,\dots,4$), and $\epsilon_1,\epsilon_2\in C([0,1])$ with $\epsilon_1,\epsilon_2>0$. Then there exists a unique solution $F=(F^1,\dots,F^4)\in C(\mathcal T)^4$, in the following sense: for every $j$ and every $(x,\xi)\in\mathcal T$,
--   $$F^j(x,\xi)=F^j\big(x_j(x,\xi,0),\xi_j(x,\xi,0)\big)+\int_0^{s_j^F(x,\xi)}\Big[g_j+\sum_{i=1}^4C_{ji}F^i\Big]\big(x_j(x,\xi,s),\xi_j(x,\xi,s)\big)\,ds,$$
--   where $(x_j,\xi_j)$, $s\in[0,s_j^F]$, are the characteristic curves (A.9)–(A.20), and the boundary conditions (A.5)–(A.7) hold on $[0,1]$. Existence and uniqueness are both asserted; uniqueness is among continuous solutions and concerns values on $\mathcal T$.
--
--   In the paper this theorem guarantees that the backstepping kernel equations (3.30)–(3.37), which are instances of this system, have well-defined continuous solutions.
--
--   **Formalization Note** A merely continuous $F$ cannot satisfy the first-order system (A.1)–(A.4) pointwise; the paper's solution, constructed in §A.1–A.3, is the solution of the characteristic integral equations (A.23) together with the boundary conditions, and this is the notion `IsCharSolution` used here. A $C^1$ solution of (A.1)–(A.7) satisfies these integral equations, by integrating along each characteristic. The data are functions on $\mathbb R$ or $\mathbb R^2$ with hypotheses imposed on $[0,1]$ or $\mathcal T$ only; values of $F$ off $\mathcal T$ are irrelevant, so uniqueness is stated pointwise on $\mathcal T$. No differentiability of $\epsilon_i$ is assumed, as in the paper.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 19, Theorem A.1; integral interpretation (A.23), p. 20

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

namespace HyperbolicBackstepping.Kernel

/-- Theorem A.1, p. 19: existence and uniqueness of a continuous solution to
the characteristic integral form of (A.1)–(A.7). -/
theorem theorem_A_1 (D : GoursatData) :
    (∃ F : Fin 4 → ℝ → ℝ → ℝ,
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) Tri) ∧
        IsCharSolution D F) ∧
    (∀ F F' : Fin 4 → ℝ → ℝ → ℝ,
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) Tri) →
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F' j p.1 p.2) Tri) →
      IsCharSolution D F → IsCharSolution D F' →
      ∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri → F j x ξ = F' j x ξ) := by sorry

end HyperbolicBackstepping.Kernel
