-- Prove2me | Theorems.Thm_NesterovRCD_Constrained_eq_4_4
-- name    : NesterovRCD.Constrained.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:20.678742+00:00
-- url     : https://prove2.me/theorems/78b367af-da20-4d84-8fb4-5cc5b22be2a8
-- title:
--   (4.4) — $f(x)-f(V_i(x))\ge\frac{L_i}2\|u^{(i)}(x)-x^{(i)}\|_{(i)}^2$
-- statement:
--   In the setting of §4 — $Q=Q_1\times\cdots\times Q_n$ with each $Q_i\subseteq\mathbb R^{n_i}$ nonempty, closed and convex, Euclidean block norms (3.4), and $f$ convex with coordinate-wise Lipschitz gradient (2.2), constants $L_i>0$ — let $u^{(i)}(x)$ and $V_i(x)=x+U_i(u^{(i)}(x)-x^{(i)})$ be the constrained coordinate update (4.2). Then for every feasible point $x\in Q$ and every block $i$,
--   $$f(x)-f(V_i(x))\ge\frac{L_i}2\,\big\|u^{(i)}(x)-x^{(i)}\big\|_{(i)}^2 .$$
--
--   Each step of the constrained method therefore does not increase the objective, and decreases it in proportion to the squared length of the step. It makes the expected values $\varphi_k$ of UCDM nonincreasing.
--
--   **Formalization Note** The paper writes $x^i$ for $x^{(i)}$ in the derivation (a typo). The hypothesis $x\in Q$ is implicit in the paper, whose derivation substitutes $u^{(i)}=x^{(i)}$ into (4.3), which requires $x^{(i)}\in Q_i$; it is stated. The standing assumptions of §4 are stated as for (4.3), together with $Q_i\ne\emptyset$ and $n\ge1$. Indices are `Fin n`, 0-based.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 13, §4, (4.4)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem eq_4_4 (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) (x : NesterovRCD.Sublinear.Blocks E) (hx : x ∈ Qset Q) (i : Fin n) :
    L i / 2 * ‖blockUpdate f L Q x i - x i‖ ^ 2 ≤ f x - f (constrStep f L Q i x) := by sorry

end NesterovRCD.Constrained
