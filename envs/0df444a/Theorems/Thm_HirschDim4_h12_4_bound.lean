-- Prove2me | Theorems.Thm_HirschDim4_h12_4_bound
-- name    : HirschDim4.h12_4_bound
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:55:02.828979+00:00
-- url     : https://prove2.me/theorems/e51853f4-25b7-4799-b3ef-ec364a38264c
-- title:
--   $H(12,4)\le 7$ (Bremner–Deza–Hua–Schewe 2013)
-- statement:
--   Every $4$-dimensional polytope with $12$ facets has combinatorial diameter at most $7$. This is the upper-bound half of $H(12,4)=7$, proved by Bremner, Deza, Hua and Schewe (2013). Since $7<12-4=8$, it confirms the Hirsch bound for $(n,d)=(12,4)$ — the last verified facet count in dimension $4$. Consequently any $4$-dimensional counterexample must have at least $13$ facets.
--
--   **Formalization Note.** Bounded facet presentation hypotheses; conclusion `DiamLE (Hpoly a b) 7`.
-- source:
--   D. Bremner, A. Deza, W. Hua & L. Schewe, More bounds on the diameters of convex polytopes, Optimization Methods and Software 28(3) (2013), 442-450, https://doi.org/10.1080/10556788.2012.668906 (Delta(4,12)=7); Kim & Santos survey arXiv:0907.1186, Theorem 2.2 (bullet 5). Upper-bound half.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem h12_4_bound (a : Fin 12 → EuclideanSpace ℝ (Fin 4)) (b : Fin 12 → ℝ)
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 7 := by sorry

end HirschDim4
