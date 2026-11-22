-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryIndependentIncrementsV1
-- name    : Kyprianou.Ch01.inverseGaussianZeroBoundaryIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:03:32.88259+00:00
-- url     : https://prove2.me/theorems/d9094b94-0d60-4da7-8aad-8dd0be7c894f
-- title:
--   §1.2.5: Brownian passage subordinator IndependentIncrements
-- statement:
--   Strong Markov property gives independent increments of the first passage process indexed by the positive barrier level. The zero barrier time is pathwise zero.
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

theorem Kyprianou.Ch01.inverseGaussianZeroBoundaryIndependentIncrementsV1
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
    ProbabilityTheory.HasIndependentIncrements T P := by
  sorry
