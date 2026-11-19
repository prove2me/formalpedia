-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exponentRegularity_strictConvexNontrivial
-- name    : Kyprianou.Ch03.exponentRegularity_strictConvexNontrivial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:15.286027+00:00
-- url     : https://prove2.me/theorems/aaa96a3a-115f-4dcd-ad1f-935511f73d8b
-- title:
--   Exercise 3.5 part 4: strictConvexNontrivial
-- statement:
--   The full original mathematical subpart 4 of Exercise 3.5, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.5, part 4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exponentRegularity_strictConvexNontrivial
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ((0 < L.σ ∨ L.ν ≠ 0) →
      StrictConvexOn ℝ (Set.Ioi 0) L.ψ) := by
  sorry

end Kyprianou.Ch03
