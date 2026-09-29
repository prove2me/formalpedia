-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_projection
-- name    : LinearOptimization.polyhedron_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T01:18:34.873541+00:00
-- url     : https://prove2.me/theorems/5f00401c-20fe-404a-b0f3-718e95e40d10
-- title:
--   Projections of polyhedra are polyhedra
-- statement:
--   **(Corollary 2.4)** Let $P \subset \mathbb{R}^{n+k}$ be a polyhedron. Then, the set
--
--   $$\{x \in \mathbb{R}^n \mid \text{there exists } y \in \mathbb{R}^k \text{ such that } (x, y) \in P\}$$
--
--   is also a polyhedron.
--
--   (Equivalently, by repeated application of the elimination algorithm, every projection $\Pi_k(P)$ of a polyhedron is a polyhedron.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 2.4, p. 74

import Definitions.Def_Polyhedron


/-- **Bertsimas & Tsitsiklis, Corollary 2.4 (p. 74).** The projection of a polyhedron
`P ⊆ ℝ^{n+k}` onto its first `n` coordinates is a polyhedron: it admits a
general-form presentation `{x | A'x ≥ b'}`. -/

theorem LinearOptimization.polyhedron_projection {m n k : ℕ}
    (A : Matrix (Fin m) (Fin (n + k)) ℝ) (b : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      {x : Fin n → ℝ | ∃ y : Fin k → ℝ, Fin.append x y ∈ polyhedron A b} =
        polyhedron A' b' := by
  sorry
