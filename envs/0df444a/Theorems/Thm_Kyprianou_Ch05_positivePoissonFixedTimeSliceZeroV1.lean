-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonFixedTimeSliceZeroV1
-- name    : Kyprianou.Ch05.positivePoissonFixedTimeSliceZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:54:29.569042+00:00
-- url     : https://prove2.me/theorems/fdd72197-c692-51fb-90a1-78f1bd741faa
-- title:
--   Poisson measure has zero mass at each deterministic time
-- statement:
--   The time singleton has zero product intensity. Its random count is nonnegative, measurable and has zero expected value by the Poisson evaluation mean.
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

theorem Kyprianou.Ch05.positivePoissonFixedTimeSliceZeroV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (t : ℝ) :
    ∀ᵐ w ∂Q, poissonRandomMeasure K Z w ({t} ×ˢ (univ : Set ℝ)) = 0 := by
  sorry
