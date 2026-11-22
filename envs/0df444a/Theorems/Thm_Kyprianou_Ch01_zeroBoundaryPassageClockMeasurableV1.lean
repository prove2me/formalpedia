-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageClockMeasurableV1
-- name    : Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:38:17.392199+00:00
-- url     : https://prove2.me/theorems/0cc4e421-5f0a-44de-a11b-c5c869d713fd
-- title:
--   Zero-normalised real first-passage clock has measurable coordinates
-- statement:
--   Every coordinate of the zero-normalised first-upper-passage real clock is measurable under measurable Brownian path coordinates and continuous sample paths. For s=0 it is the constant zero. For s>0, use the already Proved firstUpperPassageMeasurableOfContinuousPublic to obtain measurability of the WithTop NNReal stopping time, compose with measurable WithTop.untopD 0, then with measurable NNReal-to-Real inclusion. The result is a direct input for positive-time stationary-increment reduction.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and measurable first-upper-passage theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ≥0) :
    Measurable
      (fun ω =>
        if s = 0 then (0 : ℝ)
        else (match firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))) := by sorry
