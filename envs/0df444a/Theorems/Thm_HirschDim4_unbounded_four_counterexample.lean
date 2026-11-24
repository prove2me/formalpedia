-- Prove2me | Theorems.Thm_HirschDim4_unbounded_four_counterexample
-- name    : HirschDim4.unbounded_four_counterexample
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T22:56:11.609517+00:00
-- url     : https://prove2.me/theorems/42b2f5d3-dcdd-4cba-9897-3ff27fd02e28
-- title:
--   The unbounded Hirsch conjecture fails in dimension $4$ (Klee–Walkup 1967)
-- statement:
--   The **unbounded** Hirsch conjecture fails in dimension $4$: there is a simple, unbounded $4$-dimensional polyhedron with $8$ facets and two vertices at graph distance at least $5>8-4=4$. It is obtained from the Hirsch-sharp polytope $Q_4$ ($9$ facets, diameter $5$) by a projective transformation sending a facet containing neither vertex to infinity; this preserves the distance but destroys boundedness. This is why the bounded problem in dimension $4$ remains open while its unbounded and monotone variants already fail. This milestone targets the non-Hirsch (lower-bound) part of the source theorem, which states diameter exactly $5$.
--
--   **Formalization Note.** Uses `KleeWalkup67.FiveStep.IsFacetPresentation` and `IsSimple` (the latter requires a vertex and exactly $d$ tight facets at each vertex); `¬ IsBounded` records unboundedness; `∀ k<5, ¬ Reach ... k u v` is distance $\ge 5$.
-- source:
--   Kim & Santos, An update on the Hirsch conjecture, arXiv:0907.1186, Theorem 3.14, attributing to V. Klee & D. W. Walkup, Acta Math. 117 (1967), 53-78, https://doi.org/10.1007/BF02395040. Non-Hirsch (lower-bound) part; the source states diameter exactly 5.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace HirschDim4

theorem unbounded_four_counterexample :
    ∃ (a : Fin 8 → EuclideanSpace ℝ (Fin 4)) (b : Fin 8 → ℝ)
      (u v : EuclideanSpace ℝ (Fin 4)),
      KleeWalkup67.FiveStep.IsFacetPresentation a b ∧
      KleeWalkup67.FiveStep.IsSimple a b ∧
      ¬ Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
      v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
      ∀ k < 5, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k u v := by sorry

end HirschDim4
