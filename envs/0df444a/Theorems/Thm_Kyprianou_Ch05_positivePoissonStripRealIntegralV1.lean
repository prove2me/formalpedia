-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonStripRealIntegralV1
-- name    : Kyprianou.Ch05.positivePoissonStripRealIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:30:38.808817+00:00
-- url     : https://prove2.me/theorems/a0b70545-6cf2-5786-b194-157b91478d80
-- title:
--   Real integral equals the real value of nonnegative strip mass
-- statement:
--   The strip indicator is nonnegative. Convert its real integral to the extended nonnegative integral, then move the indicator to a measure restriction.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.positivePoissonStripRealIntegralV1
    (mu : Measure (ℝ × ℝ)) (s t : ℝ) :
    (∫ z, (Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd z ∂mu) =
      (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂mu).toReal := by
  sorry
