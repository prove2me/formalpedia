-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianPositiveBarrierStationaryIncrementV1
-- name    : Kyprianou.Ch01.inverseGaussianPositiveBarrierStationaryIncrementV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T00:38:55.1887+00:00
-- url     : https://prove2.me/theorems/255cb1dd-eb45-4b86-b317-6d7c66ac9059
-- title:
--   Positive-spatial-level first-passage increments have stationary law under Brownian strong Markov
-- statement:
--   For a unit-volatility positive-drift Brownian Lévy process and strictly positive barrier s and spatial step h, the level-indexed first-upper-passage clock increment T(s+h)-T(s) has the same distribution as T(h)-T(0). This is the nontrivial positive-positive stationarity step. A sound proof uses the Brownian strong Markov property at the finite passage time T(s), spatial homogeneity X_{T(s)}=s, and deterministic first-passage time-shift additivity. The other stationary-increment boundary cases are handled separately by the generic positive-pair reduction.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, strong Markov property at first Brownian passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianPositiveBarrierStationaryIncrementV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s h : ℝ≥0) (hs : 0 < s) (hh : 0 < h) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun u ω =>
        if u = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    IdentDistrib (ProbabilityTheory.increment T s (s + h))
      (ProbabilityTheory.increment T 0 h) P P := by sorry
