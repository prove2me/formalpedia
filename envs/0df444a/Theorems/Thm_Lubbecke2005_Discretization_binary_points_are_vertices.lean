-- Prove2me | Theorems.Thm_Lubbecke2005_Discretization_binary_points_are_vertices
-- name    : Lubbecke2005.Discretization.binary_points_are_vertices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T14:52:00.681784+00:00
-- url     : https://prove2.me/theorems/a85922d4-f3a5-4291-87b6-878f104a7a15
-- title:
--   Remark in §3.3 — if $X \subseteq [0,1]^n$, every point of $X$ is a vertex of $\mathrm{conv}(X)$
-- statement:
--   Let $D$ be a rational $m \times n$ matrix and $\mathbf d$ a rational $m$-vector, let $P = \{\mathbf x \in \mathbb R^n \mid D\mathbf x \geqslant \mathbf d,\ \mathbf x \geqslant \mathbf 0\}$ and $X = P \cap \mathbb Z^n$. Suppose $X \subseteq [0,1]^n$, so that $X \subseteq \{0,1\}^n$. Then every point of $X$ is a vertex of the convex hull of $X$:
--
--   $$
--   X \subseteq \operatorname{ext}\bigl(\operatorname{conv}(X)\bigr).
--   $$
--
--   In this case the discretization (24) and the convexification (23) of the integer program coincide: every integer point is itself one of the extreme points $\mathbf p_q$, so it is the trivial convex combination of one vertex. This is why many set-partitioning and set-covering decompositions need no separate discretization.
--
--   **Formalization Note** "Vertices of conv(X)" is read as the extreme points of the convex hull (`Set.extremePoints ℝ (convexHull ℝ X)`); since $X$ is finite here, conv(X) is a polytope, whose vertices and extreme points coincide. The statement assumes neither $P \neq \emptyset$ nor anything about $D$ beyond the setting of Theorem 1; the paper states the Remark for the $X$ of Theorem 1.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1012, Remark in §3.3 (second sentence)

import Mathlib
import Definitions.Def_Lubbecke2005_Discretization_Polyhedron

namespace Lubbecke2005.Discretization

/-- **Lübbecke–Desrosiers 2005, Remark in §3.3 (p. 1012).** In the special case
`X ⊆ [0, 1]ⁿ`, where `X = P ∩ ℤⁿ` and `P = {𝐱 ∈ ℝⁿ | D𝐱 ⩾ 𝐝, 𝐱 ⩾ 𝟎}`, every point of `X`
is a vertex (extreme point) of `conv(X)`. -/
theorem binary_points_are_vertices {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ)
    (d : Fin m → ℚ)
    (hX : ∀ x ∈ integerPoints D d, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ integerPoints D d,
      x ∈ Set.extremePoints ℝ (convexHull ℝ (integerPoints D d)) := by sorry

end Lubbecke2005.Discretization
