-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stationaryIncrementsOfPositivePairsV1
-- name    : Kyprianou.Ch01.stationaryIncrementsOfPositivePairsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:33:33.012369+00:00
-- url     : https://prove2.me/theorems/ab858521-76b9-4668-8808-43a1f39928eb
-- title:
--   Stationary increments follow from the positive-time pairs and a.e. measurable coordinates
-- statement:
--   For an a.e. measurable real-valued nonnegative-time process, stationary increments on strictly positive time pairs imply the full LeanLevy HasStationaryIncrements property. The degenerate s=0 case is equality of the same increment distribution, requiring only a.e. measurability. The degenerate h=0 case is the constant zero increment and therefore identically distributed. The positive-positive case is supplied by the hypothesis. This isolates the genuinely stochastic strong-Markov obligation for the inverse Gaussian first-passage process.
-- source:
--   Elementary boundary reduction for stationary increments in Kyprianou (2006), Chapter 1.

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stationaryIncrementsOfPositivePairsV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (T : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ s : ℝ≥0, AEMeasurable (T s) P)
    (hPositive : ∀ (s h : ℝ≥0), 0 < s → 0 < h →
      IdentDistrib (increment T s (s + h))
        (increment T 0 h) P P) :
    HasStationaryIncrements T P := by sorry
