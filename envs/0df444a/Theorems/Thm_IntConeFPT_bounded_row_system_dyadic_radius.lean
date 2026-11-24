-- Prove2me | Theorems.Thm_IntConeFPT_bounded_row_system_dyadic_radius
-- name    : IntConeFPT.bounded_row_system_dyadic_radius
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-24T14:27:33.986515+00:00
-- url     : https://prove2.me/theorems/9ac3aaa4-2ad7-4966-9982-3ad9f78c2582
-- title:
--   A dyadic coordinate bound for bounded rational inequality systems
-- statement:
--   Consider a bounded polyhedron given by $Ax+Bu\le b$ over the rationals. Let $s$ be one plus the total encoded length of the two matrices and the right-hand side. There is an absolute exponent $a$ such that every coordinate of every point of this polyhedron has absolute value at most $2^{s^a}$. The claim is vacuous for an empty polyhedron. This is the geometric part of the box bound: clear denominators in the tight constraints at a vertex and apply Cramer’s rule, then take convex combinations of vertices.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §2, (2.1), p. 6. Geometric ingredient: Schrijver, Theory of Linear and Integer Programming (1986), Theorem 10.3; the dyadic majorant is a coarse encoding-specific consequence.

import Definitions.Def_IntConeFPT_Instance

open OnlineCRS.Combine RobustToDynamics IntConeFPT

theorem IntConeFPT.bounded_row_system_dyadic_radius :
    ∃ a : ℕ, ∀ {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ)
      (B : Matrix (Fin m) (Fin k) ℚ) (b : Fin m → ℚ),
      let P : Set ((Fin d → ℝ) × (Fin k → ℝ)) :=
        {p | ∀ i, (∑ j, (A i j : ℝ) * p.1 j) + (∑ j, (B i j : ℝ) * p.2 j) ≤ (b i : ℝ)}
      Bornology.IsBounded P → ∀ p ∈ P,
        InBox (2 ^ ((1 + (encMat A ++ encMat B ++ encVec b).length) ^ a)) p := by sorry
