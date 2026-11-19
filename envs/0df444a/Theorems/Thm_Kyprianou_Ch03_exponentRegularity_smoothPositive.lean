-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exponentRegularity_smoothPositive
-- name    : Kyprianou.Ch03.exponentRegularity_smoothPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:12.675196+00:00
-- url     : https://prove2.me/theorems/9cfa0d35-b1f7-4501-a12e-8296936dcbca
-- title:
--   Exercise 3.5 part 2: smoothPositive
-- statement:
--   The full original mathematical subpart 2 of Exercise 3.5, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.5, part 2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exponentRegularity_smoothPositive
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) L.ψ (Set.Ioi 0) := by
  sorry

end Kyprianou.Ch03
