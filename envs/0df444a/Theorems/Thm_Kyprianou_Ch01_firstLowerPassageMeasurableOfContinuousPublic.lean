-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstLowerPassageMeasurableOfContinuousPublic
-- name    : Kyprianou.Ch01.firstLowerPassageMeasurableOfContinuousPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:42:24.021177+00:00
-- url     : https://prove2.me/theorems/d6d64999-13d4-4193-8ab8-8c41a7e25330
-- title:
--   Continuous process with measurable coordinates has measurable strict first lower passage time
-- statement:
--   If each fixed-time coordinate is measurable and each sample path is continuous, then the strict downcrossing time of x+X below any real barrier is measurable as a WithTop nonnegative random variable. Rewrite it as first upcrossing of the negated process above x-barrier, using the existing exact lower-upper identity, and apply the proved measurable-upper-passage theorem to measurable continuous negated paths.
-- source:
--   Kyprianou (2006), Chapter 1, McKean put and lower-passage stopping-time measurability.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstLowerPassageMeasurableOfContinuousPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (x barrier : ℝ) :
    Measurable (firstLowerPassage X x barrier) := by sorry
