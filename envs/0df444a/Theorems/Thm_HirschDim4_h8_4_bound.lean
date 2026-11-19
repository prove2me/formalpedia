-- Prove2me | Theorems.Thm_HirschDim4_h8_4_bound
-- name    : HirschDim4.h8_4_bound
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:54:08.851273+00:00
-- url     : https://prove2.me/theorems/b6674cdd-2427-4afd-bb3b-710ed4820887
-- title:
--   $H(8,4)\le 4$: the bounded $4$-step case (Klee 1966)
-- statement:
--   Every $4$-dimensional polytope with $8$ facets has combinatorial diameter at most $4$. This is the upper-bound half of $H(8,4)=4$, the bounded $4$-step case, proved by Klee (1966). Together with the Klee–Walkup reduction it anchors the verified range $n\le 8$ in dimension $4$; the matching lower bound is the $4$-cube.
--
--   **Formalization Note.** The hypotheses are a bounded facet presentation (`IsFacetPresentation` + `IsBounded`); the conclusion is `Hirsch.DiamLE (Hpoly a b) 4`.
-- source:
--   Kim & Santos, An update on the Hirsch conjecture, arXiv:0907.1186, Theorem 2.2 (bullet 1), attributing H(8,4)=4 to V. Klee, Paths on polyhedra II, Pacific J. Math. 17 (1966), 249-262, https://doi.org/10.2140/pjm.1966.17.249. Upper-bound half.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem h8_4_bound (a : Fin 8 → EuclideanSpace ℝ (Fin 4)) (b : Fin 8 → ℝ)
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 4 := by sorry

end HirschDim4
