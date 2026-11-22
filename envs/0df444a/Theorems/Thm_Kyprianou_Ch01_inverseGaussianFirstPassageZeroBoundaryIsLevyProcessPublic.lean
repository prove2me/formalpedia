-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageZeroBoundaryIsLevyProcessPublic
-- name    : Kyprianou.Ch01.inverseGaussianFirstPassageZeroBoundaryIsLevyProcessPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:21:50.074523+00:00
-- url     : https://prove2.me/theorems/050477d8-0592-4d0e-875b-5e988f46c26c
-- title:
--   Inverse-Gaussian positive-drift Brownian first-passage process is Levy
-- statement:
--   For a continuous Brownian process of unit volatility and positive drift b, the level-indexed upper first-passage time process (zero at barrier level zero, with the original finite-or-zero sentinel at other levels) is a Levy process. Show stationary independent increments, measurable finite-dimensional marginals, and stochastic continuity using the strong Markov property at first passage and the almost-sure finite hitting-time result. The drifted first-passage process has inverse Gaussian increments.
-- source:
--   Kyprianou (2006) Chapter 1, inverse Gaussian subordinator from positive-drift Brownian first passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open scoped Classical
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstPassageZeroBoundaryIsLevyProcessPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ProbabilityTheory.IsLevyProcess T P := by sorry
