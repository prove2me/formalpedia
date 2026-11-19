-- Prove2me | Theorems.Thm_HirschDim4_deepmind_nineteen
-- name    : HirschDim4.deepmind_nineteen
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:56:58.514132+00:00
-- url     : https://prove2.me/theorems/b1ad4bbd-bf1f-4ceb-be30-a603779cb4b9
-- title:
--   A non-Hirsch $19$-dimensional polytope with $38$ facets (DeepMind 2025)
-- statement:
--   There is a bounded, full-dimensional $19$-dimensional polytope with $38$ facets whose combinatorial diameter is greater than $19$ (in fact at least $20$): the smallest-dimensional counterexample to the Hirsch conjecture currently known. It was found in 2025 by Google DeepMind's Hopper multi-agent system: a $5$-dimensional prismatoid of width $6$ with $24$ vertices ($12$ in each base facet), converted by Santos's spindle construction to dimension $24-5=19$ with $2\cdot 19=38$ facets. Explicit coordinates of the $24$-vertex prismatoid are given in Appendix A.13 of the source.
--
--   **Formalization Note.** `IsNonHirsch a b` is `¬ DiamLE (Hpoly a b) (38-19)`, i.e. diameter $>19$. Same shape as Santos's Corollary 1.7 with $(n,d)=(38,19)$.
-- source:
--   G. Swirszcz, A. Z. Wagner, G. Williamson et al. (Google DeepMind), Advancing Geometry with AI: Multi-agent Generation of Polytopes, arXiv:2502.05199 (2025), Section 4.1 and Appendix A.13 (24-vertex width-six 5-prismatoid; non-Hirsch polytope of dimension 19 = 24-5, the smallest known).

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem deepmind_nineteen :
    ∃ (a : Fin 38 → EuclideanSpace ℝ (Fin 19)) (b : Fin 38 → ℝ),
      (Hirsch.Hpoly a b).Nonempty ∧
      Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      SantosHirsch.Counter.IsFacetPresentation a b ∧
      SantosHirsch.Counter.IsNonHirsch a b := by sorry

end HirschDim4
