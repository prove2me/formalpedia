-- Prove2me | Theorems.Thm_HirschDim4_msw_twenty
-- name    : HirschDim4.msw_twenty
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:56:32.897857+00:00
-- url     : https://prove2.me/theorems/5a730767-e705-4cee-94d2-488196926c5b
-- title:
--   A non-Hirsch $20$-dimensional polytope with $40$ facets (Matschke–Santos–Weibel 2015)
-- statement:
--   There is a bounded, full-dimensional $20$-dimensional polytope with $40$ facets whose combinatorial diameter is greater than $20$ (in fact at least $21$): a counterexample to the Hirsch conjecture in dimension $20$. Matschke, Santos and Weibel (2015) obtained it from a $5$-dimensional prismatoid of width $6$ with only $25$ vertices, via Santos's spindle construction, which outputs dimension $25-5=20$ with $2\cdot 20=40$ facets. This lowered Santos's original counterexample dimension from $43$ to $20$; the published polytope has $36{,}442$ vertices.
--
--   **Formalization Note.** `IsNonHirsch a b` is `¬ DiamLE (Hpoly a b) (40-20)`, i.e. diameter $>20$. The statement matches the shape of Santos's Corollary 1.7 with $(n,d)=(40,20)$.
-- source:
--   B. Matschke, F. Santos & C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. (3) 110(3) (2015), 647-672, https://doi.org/10.1112/plms/pdu064, arXiv:1202.4701 (main theorem: width-six 5-prismatoids with 25 vertices; non-Hirsch 20-polytopes). Also F. Santos, Annals of Math. 176 (2012), 383-412, Theorem 1.12 (20-dimensional, 40 facets, 36442 vertices).

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem msw_twenty :
    ∃ (a : Fin 40 → EuclideanSpace ℝ (Fin 20)) (b : Fin 40 → ℝ),
      (Hirsch.Hpoly a b).Nonempty ∧
      Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      SantosHirsch.Counter.IsFacetPresentation a b ∧
      SantosHirsch.Counter.IsNonHirsch a b := by sorry

end HirschDim4
