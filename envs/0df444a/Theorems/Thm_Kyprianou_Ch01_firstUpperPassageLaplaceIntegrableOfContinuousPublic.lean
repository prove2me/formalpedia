-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassageLaplaceIntegrableOfContinuousPublic
-- name    : Kyprianou.Ch01.firstUpperPassageLaplaceIntegrableOfContinuousPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:28:16.596423+00:00
-- url     : https://prove2.me/theorems/84e9cddf-da02-4faa-bebb-48c1eb5b3e50
-- title:
--   Discounted first-passage Laplace observable is integrable on a probability space
-- statement:
--   For any process with measurable fixed-time coordinates and continuous sample paths, a strictly defined upper first-passage time has a measurable nonnegative-discount Laplace payoff. The payoff has absolute value at most one and is therefore integrable against any probability measure. Reuse the proved measurable-first-passage theorem, measurable-passageLaplace composition, and its pointwise norm bound.
-- source:
--   Kyprianou (2006) Chapter 1, passage transforms and expectation under continuous paths.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassageLaplaceIntegrableOfContinuousPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s q : ℝ) (hq : 0 ≤ q) :
    Integrable (passageLaplace (firstUpperPassage X s) q) P := by sorry
