-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfMeasurablePublic
-- name    : Kyprianou.Ch01.rationalStrictUpperPassageInfMeasurablePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:22:40.341174+00:00
-- url     : https://prove2.me/theorems/8d95af79-d7ab-43bf-844a-306c13414921
-- title:
--   The rational-observation upper first-passage infimum is measurable
-- statement:
--   For any real-valued process with measurable coordinates, take the infimum over positive rational observation times at which the process exceeds a specified barrier, with infinity contributed by observations not exceeding the barrier. This extended nonnegative random time is measurable as the countable infimum of measurable, two-valued functions. Almost-sure continuity can later identify it with the original continuous first passage time.
-- source:
--   Measure-theoretic support for Kyprianou (2006), Chapter 1 first strict upper passage.

import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.NNReal.Defs
open MeasureTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalStrictUpperPassageInfMeasurablePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω =>
      ⨅ r : ℚ,
        if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
          then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
          else ⊤) := by sorry
