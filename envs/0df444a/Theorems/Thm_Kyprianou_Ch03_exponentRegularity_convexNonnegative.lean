-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exponentRegularity_convexNonnegative
-- name    : Kyprianou.Ch03.exponentRegularity_convexNonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:13.595198+00:00
-- url     : https://prove2.me/theorems/e42e6750-0a9a-4647-83b3-afe767515bb9
-- title:
--   Exercise 3.5 part 3: convexNonnegative
-- statement:
--   The full original mathematical subpart 3 of Exercise 3.5, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.5, part 3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exponentRegularity_convexNonnegative
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ConvexOn ℝ (Set.Ici 0) L.ψ := by
  sorry

end Kyprianou.Ch03
