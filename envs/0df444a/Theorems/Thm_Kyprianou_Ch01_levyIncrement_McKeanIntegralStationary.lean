-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyIncrement_McKeanIntegralStationary
-- name    : Kyprianou.Ch01.levyIncrement_McKeanIntegralStationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:04:32.136942+00:00
-- url     : https://prove2.me/theorems/6783eea4-16f5-4311-b0c9-e07db1a0355e
-- title:
--   Lévy increment McKean transition integrals depend only on elapsed time
-- statement:
--   For a real Lévy process with the standard stationary increment law, the integral of the original McKean value after adding the increment X_t−X_s to any fixed state y equals its integral after the canonical increment X_{t−s}. Use the IsLevyProcess.stationary_increments field and its exact pathwise initial normalisation X0=0 to obtain IdentDistrib, then compose it with the already Proved Borel measurability of z ↦ mckeanValue K b phi (y+z) and apply IdentDistrib.integral_eq. This is a short directly provable necessary step of the mission-connected right-natural conditional transition identity.
-- source:
--   Kyprianou (2006) Ch1 Brownian Lévy stationary increments and transition expectations.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyIncrement_McKeanIntegralStationary
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (s t : ℝ≥0) (hst : s ≤ t)
    (K b phi y : ℝ) :
    (∫ ω, mckeanValue K b phi (y + (X t ω - X s ω)) ∂P) =
      (∫ ω, mckeanValue K b phi (y + X (t - s) ω) ∂P) := by sorry
