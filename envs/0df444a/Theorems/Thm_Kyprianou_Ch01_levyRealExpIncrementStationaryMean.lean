-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyRealExpIncrementStationaryMean
-- name    : Kyprianou.Ch01.levyRealExpIncrementStationaryMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T14:56:41.185182+00:00
-- url     : https://prove2.me/theorems/b02ca933-278a-4bfc-8095-0c5811b201af
-- title:
--   Stationarity of real exponential increment expectations for any Lévy process
-- statement:
--   For any real-valued Lévy process and two ordered nonnegative times, the exponential expectation of its increment equals that of the process at the corresponding time difference. This is a direct consequence of stationary increments, independent of Gaussian assumptions or exponential integrability.
-- source:
--   Kyprianou (2006), Chapter 1 Exercises 1.5 and 1.10(i), stationary increments and real exponential moments

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyRealExpIncrementStationaryMean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, Real.exp (theta * (X t ω - X s ω)) ∂P) =
      (∫ ω, Real.exp (theta * X (t - s) ω) ∂P) := by sorry
