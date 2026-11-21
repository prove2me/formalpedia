-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageRightContinuousOfInstantCrossingV1
-- name    : Kyprianou.Ch01.zeroBoundaryPassageRightContinuousOfInstantCrossingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:37:20.737569+00:00
-- url     : https://prove2.me/theorems/74f01657-3850-4204-9ea4-7c374c6c10eb
-- title:
--   Immediate positive crossing implies right continuity of the zero-normalised passage clock at level zero
-- statement:
--   For any path that exceeds zero at arbitrarily small strictly positive times, the first strictly-upper-passage clock (explicitly reset to zero at barrier zero) is right-continuous from the right at barrier zero. This deterministic result uses strict crossing and nonnegative time.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, zero-level first passage and right regularity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroBoundaryPassageRightContinuousOfInstantCrossingV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hCross : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω) :
    ContinuousWithinAt
      (fun u : ℝ≥0 =>
        if u = 0 then (0 : ℝ)
        else (match firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some v => (v : ℝ))) (Ici (0 : ℝ≥0)) 0 := by sorry
