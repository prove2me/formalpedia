-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedClockIntegralPerturbationV1
-- name    : Kyprianou.Ch04.boundedClockIntegralPerturbationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:04:22.152769+00:00
-- url     : https://prove2.me/theorems/f1365fe4-0f66-506a-9f88-73c220381882
-- title:
--   boundedClockIntegralPerturbationV1
-- statement:
--   boundedClockIntegralPerturbationV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), uniform finite variation error

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A common positive-time bound controls every stopped clock integral. -/

theorem Kyprianou.Ch04.boundedClockIntegralPerturbationV1 (U V : ℝ → ℝ) (T : NNReal) (d : ℝ) (hd : 0 ≤ d)
    (hU : IntegrableOn U (Ioc (0 : ℝ) (T : ℝ)) volume)
    (hV : IntegrableOn V (Ioc (0 : ℝ) (T : ℝ)) volume)
    (h : ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), |U s - V s| ≤ d) :
    ∀ t : NNReal, t ≤ T →
      |(∫ s in Icc (0 : ℝ) (t : ℝ), U s) -
        (∫ s in Icc (0 : ℝ) (t : ℝ), V s)| ≤ d * (T : ℝ) := by
  sorry
