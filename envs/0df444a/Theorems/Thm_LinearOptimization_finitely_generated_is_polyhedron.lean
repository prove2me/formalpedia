-- Prove2me | Theorems.Thm_LinearOptimization_finitely_generated_is_polyhedron
-- name    : LinearOptimization.finitely_generated_is_polyhedron
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T20:48:50.828303+00:00
-- url     : https://prove2.me/theorems/2622681b-b45d-4242-a388-f988146823c3
-- title:
--   Finitely generated sets are polyhedra (converse of the resolution theorem)
-- statement:
--   **(Theorem 4.16, converse to the resolution theorem)** A finitely generated set is a polyhedron. In particular, the convex hull of finitely many vectors is a (bounded) polyhedron.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.16, p. 183

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_FinitelyGeneratedSet


/-- **Bertsimas & Tsitsiklis, Theorem 4.16 (p. 183).** Every finitely generated set
`{Σᵢ λᵢ xⁱ + Σⱼ θⱼ wʲ | λ ≥ 0, θ ≥ 0, Σλ = 1}` admits a general-form
polyhedral presentation `{y | A'y ≥ b'}`. -/

theorem LinearOptimization.finitely_generated_is_polyhedron {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      finitelyGeneratedSet x w = polyhedron A' b' := by
  sorry
