-- Prove2me | Theorems.Thm_ModernConvex_SLemma_projective_image_path_connected
-- name    : ModernConvex.SLemma.projective_image_path_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:45.46427+00:00
-- url     : https://prove2.me/theorems/f520784e-a8b7-4477-a09c-162aaa4a17e7
-- title:
--   Proposition 4.10.2 — a sphere set linked through antipodal pairs has a path-connected projective image
-- statement:
--   Let $Y$ be a subset of the unit sphere $S^{n-1} \subset \mathbb R^n$ with the following property: for every two points $x, x' \in Y$ there is $y \in Y$ such that each of $x$ and $x'$ can be linked by a continuous curve lying in $Y$ with one of the two points $y$, $-y$. Then the image $\Phi(Y)$ under the canonical projection $\Phi : S^{n-1} \to P^{n-1}$ is linearly (path) connected: any two of its points are joined by a continuous curve inside $\Phi(Y)$. In particular, $\Phi(Y)$ is connected.
--
--   This is one of the topological facts behind Polyak's convexity theorem (SL.D). It is applied to the zero set of a quadratic form on the sphere (Proposition 4.10.4).
--
--   **Formalization Note** The sphere is `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`, the book's $S^n \subset \mathbb R^{n+1}$ with the index shifted by one. `canonicalProjection n` and `ProjSpace n` (quotient topology) are from `ModernConvex.SLemma.ProjectiveSpace`. "Linked by a continuous curve in $Y$" is Mathlib's `JoinedIn Y`. The conclusion uses the book's definitions, which allow the empty set: path-connectedness is stated pairwise (`JoinedIn`), and connectedness is `IsPreconnected`. Mathlib's `IsPathConnected` and `IsConnected` would also require nonemptiness, which the book does not assume.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 308, Proposition 4.10.2 (Exercise 4.50)

import Mathlib
import Definitions.Def_ModernConvex_SLemma_ProjectiveSpace

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, Proposition 4.10.2, p. 308: let `Y` be a subset of the unit sphere such
that for every two points `x, x' ∈ Y` there is `y ∈ Y` such that each of `x`, `x'` can be linked
by a continuous curve in `Y` with `y` or with `-y`. Then `Φ(Y)` is linearly (path) connected,
and thus connected. The book's sphere `Sⁿ ⊂ ℝⁿ⁺¹` is written here `Sⁿ⁻¹ ⊂ ℝⁿ`; "linearly
connected" and "connected" are the book's notions, which allow the empty set. -/
theorem projective_image_path_connected {n : ℕ}
    (Y : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hY : ∀ x ∈ Y, ∀ x' ∈ Y, ∃ y ∈ Y, (JoinedIn Y x y ∨ JoinedIn Y x (-y)) ∧
      (JoinedIn Y x' y ∨ JoinedIn Y x' (-y))) :
    (∀ p ∈ canonicalProjection n '' Y, ∀ q ∈ canonicalProjection n '' Y,
        JoinedIn (canonicalProjection n '' Y) p q) ∧
      IsPreconnected (canonicalProjection n '' Y) := by sorry

end ModernConvex.SLemma
