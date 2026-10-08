-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Kernel_lemma_A_3
-- name    : HyperbolicBackstepping.Kernel.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:29.608588+00:00
-- url     : https://prove2.me/theorems/6ebb67ec-ffec-4166-91c2-98811313e544
-- title:
--   Lemma A.3, p. 19 — characteristic confinement, order, and continuity
-- statement:
--   Let $x_i,\xi_i,s_i^F$ ($i=1,\dots,4$) be the characteristic curves and terminal parameters (A.9)–(A.20) of the Goursat system on $\mathcal T=\{(x,\xi):0\le\xi\le x\le1\}$, built from continuous positive speeds $\epsilon_1,\epsilon_2$.
--
--   1. For every $(x,\xi)\in\mathcal T$ one has $s_i^F(x,\xi)\ge0$, and for every $s\in[0,s_i^F(x,\xi)]$ the point $(x_i(x,\xi,s),\xi_i(x,\xi,s))$ lies in $\mathcal T$.
--   2. On these parameter ranges,
--   $$x_i(x,\xi,s)\le x\ (i=1,\dots,4),\qquad \xi_1(x,\xi,s),\ \xi_4(x,\xi,s)\le\xi,\qquad \xi_2(x,\xi,s),\ \xi_3(x,\xi,s)\ge\xi.\qquad\text{(A.21)–(A.22)}$$
--   3. $s_i^F$ is continuous on $\mathcal T$, and $x_i,\xi_i$ are continuous on their domain of definition $\{((x,\xi),s):(x,\xi)\in\mathcal T,\ 0\le s\le s_i^F(x,\xi)\}$.
--
--   These facts keep every characteristic integral of the successive-approximation scheme inside the triangle, and supply the monotonicity $x_i\le x$ that drives the factorial estimates.
--
--   **Formalization Note** The nonnegativity $s_i^F\ge0$ is implicit in the paper's interval $[0,s_i^F]$ and is stated explicitly. Lean indices $0,3$ are the paper's curves $1,4$, and $1,2$ are curves $2,3$.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 19, Lemma A.3 and (A.21)–(A.22)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

namespace HyperbolicBackstepping.Kernel

/-- Lemma A.3, p. 19: characteristic confinement, order, and continuity. -/
theorem lemma_A_3 (D : GoursatData) :
    (∀ j : Fin 4, ContinuousOn (fun p : ℝ × ℝ => sF D j p.1 p.2) Tri) ∧
    (∀ j : Fin 4, ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ => charX D j p.1.1 p.1.2 p.2) (CharDomain D j)) ∧
    (∀ j : Fin 4, ContinuousOn
      (fun p : (ℝ × ℝ) × ℝ => charXi D j p.1.1 p.1.2 p.2) (CharDomain D j)) ∧
    (∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri →
      0 ≤ sF D j x ξ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) (sF D j x ξ),
        (charX D j x ξ s, charXi D j x ξ s) ∈ Tri ∧
        charX D j x ξ s ≤ x ∧
        ((j = 0 ∨ j = 3) → charXi D j x ξ s ≤ ξ) ∧
        ((j = 1 ∨ j = 2) → ξ ≤ charXi D j x ξ s)) := by sorry

end HyperbolicBackstepping.Kernel
