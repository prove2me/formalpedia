-- Prove2me | Theorems.Thm_JaggiFW_Sparsity_support_convexHull
-- name    : JaggiFW.Sparsity.support_convexHull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:23.539354+00:00
-- url     : https://prove2.me/theorems/d1d379d5-bff9-47e4-8c0e-b16ef25783b8
-- title:
--   Support function of an atomic set equals that of its convex hull
-- statement:
--   Let $A$ be a set of atoms in a real inner product space, and let $y$ be a vector. For every real $c$,
--   $$
--   (\forall s\in\operatorname{conv}(A),\ \langle s,y\rangle\le c)
--   \quad\Longleftrightarrow\quad
--   (\forall a\in A,\ \langle a,y\rangle\le c).
--   $$
--   When $A$ is finite and nonempty, some atom attains the largest inner product over the whole convex hull. Thus the support function of $A$ and of its convex hull agree, and in the finite case their common value is attained.
--
--   **Formalization Note** The attained point is stated as an atom in $A$; the paper calls it a vertex. The bound formulation of support equality also handles empty or unbounded atomic sets without assigning a default real supremum.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), PDF p. 5, §4 "Optimizing over Atomic Sets", support-function paragraph

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

namespace JaggiFW.Sparsity

/-- The support of an atomic set agrees with that of its convex hull (§4, PDF p. 5). -/
theorem support_convexHull {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Set E) (y : E) :
    (∀ c : ℝ, (∀ s ∈ convexHull ℝ A, inner ℝ s y ≤ c) ↔
      (∀ a ∈ A, inner ℝ a y ≤ c)) ∧
    (A.Finite → A.Nonempty →
      ∃ a ∈ A, IsGreatest ((fun s => inner ℝ s y) '' convexHull ℝ A) (inner ℝ a y)) := by sorry

end JaggiFW.Sparsity
