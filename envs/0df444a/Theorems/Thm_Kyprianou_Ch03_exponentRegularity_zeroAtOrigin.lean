-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exponentRegularity_zeroAtOrigin
-- name    : Kyprianou.Ch03.exponentRegularity_zeroAtOrigin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:15.735206+00:00
-- url     : https://prove2.me/theorems/979f9d3a-6c1e-469a-8769-1ec9b3a42f75
-- title:
--   Exercise 3.5 part 1: zeroAtOrigin
-- statement:
--   The full original mathematical subpart 1 of Exercise 3.5, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.5, part 1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exponentRegularity_zeroAtOrigin
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    L.ψ 0 = 0 := by
  sorry

end Kyprianou.Ch03
