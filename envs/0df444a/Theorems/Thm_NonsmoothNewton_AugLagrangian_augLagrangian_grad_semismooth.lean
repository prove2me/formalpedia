-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_augLagrangian_grad_semismooth
-- name    : NonsmoothNewton.AugLagrangian.augLagrangian_grad_semismooth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:54:11.339749+00:00
-- url     : https://prove2.me/theorems/cc48fc7a-4a9f-4a2a-a392-438459c22b2e
-- title:
--   Theorem 4.1 — the augmented Lagrangian $L_r$ is $C^1$, with gradient semismooth on the surfaces $y_i + r f_i(x) = 0$ and smooth elsewhere
-- statement:
--   Consider the nonlinear program (4.1) with $x \in \mathbb{R}^n$, objective $f_0$, equality constraints $f_i(x) = 0$ for $i = 1, \dots, p$ and inequality constraints $f_i(x) \le 0$ for $i = p+1, \dots, m$, and assume $f_0, f_1, \dots, f_m$ are of class $C^2$ on $\mathbb{R}^n$. Let $r > 0$ and let $L_r(x, y)$, $(x, y) \in \mathbb{R}^n \times \mathbb{R}^m$, be the augmented Lagrangian
--   $$
--   L_r(x, y) = f_0(x) + \sum_{i=1}^{p} \Big( y_i f_i(x) + \tfrac12 r f_i(x)^2 \Big) + \sum_{i=p+1}^{m} \phi\big(r, f_i(x), y_i\big).
--   $$
--   Then:
--   1. $L_r$ is continuously differentiable on $\mathbb{R}^n \times \mathbb{R}^m$;
--   2. $\nabla L_r$ is semismooth at every $(x, y)$ such that $y_i + r f_i(x) = 0$ for at least one inequality index $i \in \{p+1, \dots, m\}$;
--   3. $\nabla L_r$ is continuously differentiable in a neighbourhood of every $(x, y)$ such that $y_i + r f_i(x) \neq 0$ for all $i \in \{p+1, \dots, m\}$.
--
--   In the paper's words: $L_r \in C^1$, $\nabla L_r$ is semismooth on the "surfaces" where $y_i + r f_i(x) = 0$ for $i = p+1, \dots, m$, and smooth in other places. Consequently the generalized-Jacobian Newton method, whose local superlinear convergence the paper proves for semismooth equations, can be applied to $\nabla L_r = 0$ in the augmented Lagrangian method, although $L_r$ is not twice differentiable.
--
--   **Formalization Note** $\nabla L_r$ is the Fréchet derivative map $z \mapsto DL_r(z)$, valued in linear functionals on $\mathbb{R}^n \times \mathbb{R}^m$; it corresponds to the gradient vector through the Riesz isometry, and semismoothness is invariant under that isometry and under equivalent norms on the domain. "Smooth" is the paper's continuously differentiable, stated as `ContDiffAt ℝ 1` of $\nabla L_r$ at the point. The constraint index is `i : Fin m` (paper index `i.val + 1`); inequality indices are those with `p ≤ i.val`. $C^2$ is `ContDiff ℝ 2` on all of $\mathbb{R}^n$. The paper's implicit $p \le m$ is not assumed; for $p > m$ there are no inequality constraints and clause 2 is vacuous.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 363, Theorem 4.1

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Qi–Sun (1993), Theorem 4.1, p. 363. Let `r > 0` and `f₀, f₁, …, f_m ∈ C²` on `ℝⁿ`, with
constraints `1, …, p` equalities and `p + 1, …, m` inequalities (Lean: `i : Fin m` is an
inequality iff `p ≤ i.val`). Then
1. the augmented Lagrangian `L_r` is `C¹` on `ℝⁿ × ℝᵐ`;
2. `∇L_r` is semismooth at every `(x, y)` with `y_i + r f_i(x) = 0` for some inequality
   index `i`;
3. `∇L_r` is `C¹` near every `(x, y)` with `y_i + r f_i(x) ≠ 0` for all inequality indices. -/
theorem augLagrangian_grad_semismooth {n m : ℕ} (p : ℕ) (r : ℝ) (hr : 0 < r)
    (f0 : EuclideanSpace ℝ (Fin n) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ContDiff ℝ 2 f0) (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 1 (augLagrangian p r f0 f) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      (∃ i : Fin m, p ≤ i.val ∧ y i + r * f i x = 0) →
        SemismoothAt (fun z => fderiv ℝ (augLagrangian p r f0 f) z) (x, y)) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      (∀ i : Fin m, p ≤ i.val → y i + r * f i x ≠ 0) →
        ContDiffAt ℝ 1 (fun z => fderiv ℝ (augLagrangian p r f0 f) z) (x, y)) := by sorry

end NonsmoothNewton.AugLagrangian
