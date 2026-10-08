-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_eq_8
-- name    : GivenDegreeSeq.FixedPoint.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:34.133534+00:00
-- url     : https://prove2.me/theorems/8bfdf4fd-b4dd-4fd0-97cd-6983c7ba51d4
-- title:
--   (8) — $\varphi(x)-\varphi(y)=J(x,y)(x-y)$, with $\partial\varphi_i/\partial x_j<0<\partial\varphi_i/\partial x_i$ and $\sum_j|\partial\varphi_i/\partial x_j|\equiv1$
-- statement:
--   Let $n\ge2$, $d_1,\dots,d_n>0$, let $\varphi$ be the map of (5), and let $J(x,y)$ be the matrix with entries $J_{ij}(x,y)=\int_0^1\frac{\partial\varphi_i}{\partial x_j}(tx+(1-t)y)\,dt$. Then:
--
--   1. for all $x,y\in\mathbb R^n$,
--   $$\varphi(x)-\varphi(y)=J(x,y)(x-y);\tag{8}$$
--   2. for each $i\ne j$, $\partial\varphi_i/\partial x_j$ is negative everywhere;
--   3. for each $i$, $\partial\varphi_i/\partial x_i$ is positive everywhere;
--   4. for each $i$ and every $z\in\mathbb R^n$,
--   $$\sum_{j=1}^n\left|\frac{\partial\varphi_i}{\partial x_j}(z)\right|=1.$$
--
--   Together these say that every row of $J(x,y)$ has absolute sum exactly $1$, so $|J(x,y)|_\infty=1$ and $\varphi$ is non-expansive in the sup norm.
--
--   **Formalization Note** $J(x,y)(x-y)$ is the matrix–vector product. The hypothesis $n\ge2$ is needed for the row-sum identity (for $n=1$, $\varphi$ is constant). Vertices are indexed by `Fin n`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 12–13, definition of J(x,y) and Eq. (8)

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.FixedPoint

/-- (8) and the row sums, pp. 12–13: `φ(x) − φ(y) = J(x, y)(x − y)`; for `i ≠ j`,
`∂φ_i/∂x_j < 0` everywhere; `∂φ_i/∂x_i > 0` everywhere; and
`Σ_j |∂φ_i/∂x_j| = 1` everywhere. -/
theorem eq_8 {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    (∀ x y : Fin n → ℝ, phi d x - phi d y = (J d x y).mulVec (x - y)) ∧
    (∀ (z : Fin n → ℝ) (i j : Fin n), i ≠ j → partialPhi d z i j < 0) ∧
    (∀ (z : Fin n → ℝ) (i : Fin n), 0 < partialPhi d z i i) ∧
    (∀ (z : Fin n → ℝ) (i : Fin n), ∑ j : Fin n, |partialPhi d z i j| = 1) := by sorry

end GivenDegreeSeq.FixedPoint
