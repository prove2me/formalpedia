-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassageMeasurableOfContinuousPublic
-- name    : Kyprianou.Ch01.firstUpperPassageMeasurableOfContinuousPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:26:00.876951+00:00
-- url     : https://prove2.me/theorems/6d06f7df-f059-4757-98d3-608fbaec7bfc
-- title:
--   Continuous paths with measurable coordinates have a measurable first upper passage time
-- statement:
--   For a stochastic real-valued process with measurable fixed-time coordinates and continuous sample paths, the first strict upper passage time into any real barrier is a measurable WithTop nonnegative random variable. Prove by the already Proved pointwise equality with the countable rational crossing infimum and the already Proved measurability of that countable infimum.
-- source:
--   Kyprianou (2006), Chapter 1, first-passage stopping times and rational approximation of strict upcrossings.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassageMeasurableOfContinuousPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) :
    Measurable (firstUpperPassage X s) := by sorry
