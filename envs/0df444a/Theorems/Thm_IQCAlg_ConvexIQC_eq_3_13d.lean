-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_eq_3_13d
-- name    : IQCAlg.ConvexIQC.eq_3_13d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:46.326043+00:00
-- url     : https://prove2.me/theorems/18b3849c-bd26-4ae7-9aef-13c6be9fa3a0
-- title:
--   (3.13d), Proposition 5, p. 13 — the sector inequality for f ∈ S(m, L)
-- statement:
--   Let $f\in S(m,L)$, i.e. $0<m<L$ and $f:\mathbb R^d\to\mathbb R$ is continuously differentiable, $m$-strongly convex, with $L$-Lipschitz gradient. Then for all $x,y\in\mathbb R^d$,
--   $$\begin{bmatrix}y-x\\ \nabla f(y)-\nabla f(x)\end{bmatrix}^{\mathsf T}\begin{bmatrix}-2mL\,I_d&(L+m)I_d\\(L+m)I_d&-2I_d\end{bmatrix}\begin{bmatrix}y-x\\ \nabla f(y)-\nabla f(x)\end{bmatrix}\ \ge\ 0,$$
--   that is,
--   $$-2mL\|y-x\|^2+2(L+m)\,(y-x)^{\mathsf T}(\nabla f(y)-\nabla f(x))-2\|\nabla f(y)-\nabla f(x)\|^2\ \ge\ 0 .$$
--
--   This is the pointwise quadratic constraint behind the sector IQC (Lemma 6).
--
--   **Formalization Note** The block quadratic form is written expanded.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 13, Proposition 5, (3.13d)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- (3.13d), Proposition 5, p. 13, with the block quadratic form expanded. -/
theorem eq_3_13d {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) :
    ∀ x y : E d,
      0 ≤ -2 * m * L * ‖y - x‖ ^ 2
        + 2 * (L + m) * ⟪y - x, gradient f y - gradient f x⟫_ℝ
        - 2 * ‖gradient f y - gradient f x‖ ^ 2 := by sorry

end IQCAlg.ConvexIQC
