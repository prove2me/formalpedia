-- Prove2me | Theorems.Thm_HiddenConvexSO_corollary_1
-- name    : HiddenConvexSO.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:36.500314+00:00
-- url     : https://prove2.me/theorems/0d83193d-787b-4f7e-b1f5-60487c6f42a9
-- title:
--   Corollary 1 — every linear image of $\mathrm{SO}(n)$ in $\mathbb R^2$ is convex, $n\ge 3$
-- statement:
--   Let $n\ge 3$ and let $\pi:\mathbb R^{n\times n}\to\mathbb R^2$ be linear. Then the image of the special orthogonal group
--
--   $$
--   \pi\bigl(\mathrm{SO}(n)\bigr)=\{\pi(X):\ X\in\mathbb R^{n\times n},\ X^\top X=I,\ \det X=1\}\ \subseteq\ \mathbb R^2
--   $$
--
--   is convex.
--
--   Consequently any problem $\max\{\langle A,X\rangle: X\in\mathrm{SO}(n),\ \langle B,X\rangle\in[a,b]\}$ has the same value over $\mathrm{SO}(n)$ as over its convex hull, and can be solved as a convex problem in the plane. The hypothesis $n\ge 3$ is needed: for $n=2$, $X\mapsto(X_{11},X_{21})$ maps $\mathrm{SO}(2)$ onto the unit circle.
--
--   **Formalization Note** $\mathrm{SO}(n)$ is `Matrix.specialOrthogonalGroup (Fin n) ℝ` as a subset of `Matrix (Fin n) (Fin n) ℝ`; $\mathbb R^2$ is `ℝ × ℝ`; $\pi$ is any `ℝ`-linear map on all of $\mathbb R^{n\times n}$, restricted to $\mathrm{SO}(n)$ by taking the image.
--
--   Differences from the source:
--   - encoding: SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1} with the subspace topology (p.1, p.13) → Matrix.specialOrthogonalGroup (Fin n) ℝ (star A * A = 1 ∧ A * star A = 1 ∧ det A = 1), coerced subtype topology; 0-based indices; reason: Lean convention; for real square matrices AᵀA = I already gives AAᵀ = I, so the same set
--   - encoding: π : SO(n) → ℝ² linear → proj : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ × ℝ, image of SO(n); reason: SO(n) is not a vector space; a linear map on it is the restriction of a linear map on ℝ^{n×n}, as the proof's adjoint π* presupposes; every such restriction is covered
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, Corollary 1, p.12 (also stated on p.5)

import Mathlib

namespace HiddenConvexSO

/-- **Corollary 1: every linear image of SO(n) in the plane is convex, `n ≥ 3`.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, Corollary 1, p.12 (PDF p.12; also p.5): "Let n ≥ 3
and let π : SO(n) → R2 be linear, then π(SO(n)) is convex."

**Formalization Note.** SO(n) is `Matrix.specialOrthogonalGroup (Fin n) ℝ`, viewed as a subset of
`ℝ^{n×n}`; `ℝ²` is `ℝ × ℝ`. "π : SO(n) → ℝ² linear" is the restriction to SO(n) of a linear map
`proj : ℝ^{n×n} → ℝ²` (SO(n) is not a vector space; the paper's proof uses the adjoint `π*` of a
linear map on `ℝ^{n×n}`). Every `n ≥ 3` and every linear map are covered. -/
theorem corollary_1 (n : ℕ) (hn : 3 ≤ n) (proj : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ × ℝ) :
    Convex ℝ (proj '' (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ))) := by sorry

end HiddenConvexSO
