-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsCountTimeMeanV1
-- name    : Kyprianou.Ch04.klsCountTimeMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:37:35.347803+00:00
-- url     : https://prove2.me/theorems/9bde1ec7-30fd-5324-81d6-3d83c39c5571
-- title:
--   KLS finite time-mark count exact first moment
-- statement:
--   A finite KLS Poisson time-mark count is integrable and has mean equal to its time-mark reference intensity.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite marked Poisson moment calculation.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsCountTimeMeanV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (A : Set ℝ)
    (hA : MeasurableSet A) (hfinite : ν A < ⊤) (t : ℝ≥0) :
    let C := fun ω => (N.N ω (Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal
    Integrable C P ∧ (∫ ω, C ω ∂P) = (t : ℝ) * (ν A).toReal := by
  sorry
end Kyprianou.Ch04
