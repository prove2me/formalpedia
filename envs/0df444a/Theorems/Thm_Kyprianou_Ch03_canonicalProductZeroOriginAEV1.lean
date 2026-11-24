-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalProductZeroOriginAEV1
-- name    : Kyprianou.Ch03.canonicalProductZeroOriginAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:16:53.75762+00:00
-- url     : https://prove2.me/theorems/3107e933-8b87-4c85-b628-04b597ca63c5
-- title:
--   Singleton zero-origin marginal implies almost-sure zero origin
-- statement:
--   Apply the singleton time-zero projection to the measurable event that its coordinate is nonzero.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; auxiliary reductions of canonicalProductZeroOriginMarginalsV1 and canonicalPastMeasuresEqOfFiniteMarginalsV1.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalProductZeroOriginAEV1
    (μ : Measure (NNReal → ℝ))
    (M : NNReal → Measure {path : NNReal → ℝ // path 0 = 0})
    (hProj : ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) (M (I.sup id))) :
    ∀ᵐ f ∂μ, f 0 = 0 := by
  sorry
