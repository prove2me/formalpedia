-- Prove2me | Theorems.Thm_HirschDim4_h11_4_bound
-- name    : HirschDim4.h11_4_bound
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:54:33.917455+00:00
-- url     : https://prove2.me/theorems/529056e7-714f-4641-a98c-fd0b428aacd9
-- title:
--   $H(11,4)\le 6$ (Bremner–Schewe 2011)
-- statement:
--   Every $4$-dimensional polytope with $11$ facets has combinatorial diameter at most $6$. This is the upper-bound half of $H(11,4)=6$, proved by Bremner and Schewe (2011) by computer-assisted enumeration. Since $6<11-4=7$, it confirms the Hirsch bound for $(n,d)=(11,4)$.
--
--   **Formalization Note.** Bounded facet presentation hypotheses; conclusion `DiamLE (Hpoly a b) 6`.
-- source:
--   D. Bremner & L. Schewe, Edge-graph diameter bounds for convex polytopes with few facets, Experimental Mathematics 20(3) (2011), 229-237, https://doi.org/10.1080/10586458.2011.564965 (Delta(4,11)=6); Kim & Santos survey arXiv:0907.1186, Theorem 2.2 (bullet 4). Upper-bound half.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem h11_4_bound (a : Fin 11 → EuclideanSpace ℝ (Fin 4)) (b : Fin 11 → ℝ)
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 6 := by sorry

end HirschDim4
