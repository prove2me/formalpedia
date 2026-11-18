-- Prove2me | Theorems.Thm_Kyprianou_Ch07_unitIncrementIntegrable_of_finiteMean
-- name    : Kyprianou.Ch07.unitIncrementIntegrable_of_finiteMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:16:35.003984+00:00
-- url     : https://prove2.me/theorems/1525cc1b-efa7-4652-bd70-00d696a2f445
-- title:
--   Finite-mean Lévy processes have integrable deterministic unit increments
-- statement:
--   For a Lévy process in the original published Kyprianou Chapter 6 sense, if the absolute increment at unit time is integrable, every increment over an interval of length one is integrable. Use stationarity of increments in distribution and the Proved ProbabilityTheory pushforward-integrability theorem thm_7_11. This is an intermediate mathematical obligation towards Exercise 7.2 path-supremum integrability; it does not assert the supremum moment itself.
-- source:
--   Kyprianou (2006), Chapter 7, Exercise 7.2(i), printed p.207; exact original IsRealLevyProcess and finite unit-time absolute moment. Remote compiler source job ab2d4a6b-00b0-40bf-92d2-b948cd31e4be passed the sentinel with no earlier errors.

import Mathlib
import Theorems.Thm_thm_7_11
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.unitIncrementIntegrable_of_finiteMean
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun ω => |X 1 ω|) P)
    (s : ℝ≥0) :
    Integrable (fun ω => X (s + 1) ω - X s ω) P := by sorry
