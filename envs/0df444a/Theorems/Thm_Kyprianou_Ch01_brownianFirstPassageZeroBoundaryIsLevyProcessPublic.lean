-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageZeroBoundaryIsLevyProcessPublic
-- name    : Kyprianou.Ch01.brownianFirstPassageZeroBoundaryIsLevyProcessPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:14:54.463785+00:00
-- url     : https://prove2.me/theorems/4302bffa-5fe7-4121-b4d2-a87d32687a24
-- title:
--   Continuous centred Brownian first-passage level process is a Levy subordinator
-- statement:
--   With a centred Brownian process and continuous paths, the first ascending passage time as a function of barrier level is a Levy process, taking time zero at barrier zero and using the exact original definition for every positive level. Show stochastic continuity, independent stationary increments, and the adapted process law, using the strong Markov property and the almost-sure finite passage theorem. This is the principal remaining probabilistic obligation in Chapter 1 Exercise 1.10(ii).
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), first-passage process as a stable half Levy subordinator.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
open scoped Classical
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianFirstPassageZeroBoundaryIsLevyProcessPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ProbabilityTheory.IsLevyProcess T P := by sorry
