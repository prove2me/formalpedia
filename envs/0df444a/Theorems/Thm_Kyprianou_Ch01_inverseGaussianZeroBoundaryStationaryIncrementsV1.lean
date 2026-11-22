-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryStationaryIncrementsV1
-- name    : Kyprianou.Ch01.inverseGaussianZeroBoundaryStationaryIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:03:34.022189+00:00
-- url     : https://prove2.me/theorems/083a0f74-e0b1-43ae-b3ac-704bfe8cc85e
-- title:
--   §1.2.5: Brownian passage subordinator StationaryIncrements
-- statement:
--   Spatial homogeneity and strong Markov at a first-passage stopping time give stationary level increments of the first passage process.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.5, pp. 8–9, equation (1.4), and the strong Markov first-passage construction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open scoped Classical
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianZeroBoundaryStationaryIncrementsV1
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
    ProbabilityTheory.HasStationaryIncrements T P := by
  sorry
