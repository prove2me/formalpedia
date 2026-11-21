-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianPositiveLevelPassageRightContinuousOfFiniteV1
-- name    : Kyprianou.Ch01.inverseGaussianPositiveLevelPassageRightContinuousOfFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:20:39.834604+00:00
-- url     : https://prove2.me/theorems/4ea8ff3d-bbe5-41c3-87a2-236eb4ef5e6f
-- title:
--   Strict first-passage inverse is right-continuous at positive levels under finite crossing
-- statement:
--   For any real-valued path defined at nonnegative times, if every positive level has finite strictly-upper first-passage time, the real-valued first-passage function is right-continuous at all strictly positive barrier levels. The assertion is deterministic: any finite strict crossing X_t>s also crosses all nearby levels u>s.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, strict upcrossing infimum and its monotonicity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianPositiveLevelPassageRightContinuousOfFiniteV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hFinite : ∀ s : ℝ≥0, 0 < s →
      firstUpperPassage X (s : ℝ) ω ≠ ⊤) :
    ∀ s : ℝ≥0, 0 < s →
      ContinuousWithinAt
        (      fun u : ℝ≥0 =>
        if u = 0 then (0 : ℝ)
        else (match firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))) (Ici s) s := by
  sorry
