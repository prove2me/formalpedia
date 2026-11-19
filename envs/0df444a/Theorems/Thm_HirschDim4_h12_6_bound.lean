-- Prove2me | Theorems.Thm_HirschDim4_h12_6_bound
-- name    : HirschDim4.h12_6_bound
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:53:40.471205+00:00
-- url     : https://prove2.me/theorems/64e9cf3b-d627-40fa-af7d-7089dd9fcf44
-- title:
--   $H(12,6)\le 6$: the bounded $6$-step case (Bremner–Schewe 2011)
-- statement:
--   Every $6$-dimensional polytope with $12$ facets has combinatorial diameter at most $6$: the bounded $6$-step ($d$-step) case, proved by Bremner and Schewe (2011). Via the Klee–Walkup reduction this yields the Hirsch bound for all polytopes with $n-d\le 6$, and in particular $H(10,4)\le 6$.
--
--   **Formalization Note.** Bounded facet presentation hypotheses in dimension $6$; conclusion `DiamLE (Hpoly a b) 6`.
-- source:
--   D. Bremner & L. Schewe, Edge-graph diameter bounds for convex polytopes with few facets, Experimental Mathematics 20(3) (2011), 229-237, https://doi.org/10.1080/10586458.2011.564965 (Delta(6,12)=6); Kim & Santos survey arXiv:0907.1186, Theorem 2.2 (bullet 4) and Corollary 2.3. Upper-bound half.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem h12_6_bound (a : Fin 12 → EuclideanSpace ℝ (Fin 6)) (b : Fin 12 → ℝ)
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 6 := by sorry

end HirschDim4
