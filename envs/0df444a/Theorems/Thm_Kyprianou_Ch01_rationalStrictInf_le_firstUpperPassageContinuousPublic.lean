-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalStrictInf_le_firstUpperPassageContinuousPublic
-- name    : Kyprianou.Ch01.rationalStrictInf_le_firstUpperPassageContinuousPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:36:15.901778+00:00
-- url     : https://prove2.me/theorems/2103a624-c829-4971-bb9d-a17057231c33
-- title:
--   For continuous paths the rational strict upper-crossing infimum precedes the full first passage
-- statement:
--   For every continuous path, the infimum of its strictly positive rational observation times at which the path exceeds s is no later than the infimum of all strictly positive real times with a strict crossing, with infinity when no crossing exists. Whenever the full infimum is finite, continuity and density of positive rationals provide rational crossings arbitrarily close above it.
-- source:
--   Kyprianou (2006) Exercise 1.10(ii) continuous first-passage approximation. The already Proved theorem firstUpperPassage_le_iff_rationalApproachingCrossings supplies the rational approximations.

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalStrictInf_le_firstUpperPassageContinuousPublic
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω)) :
    (⨅ r : ℚ,
      if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
        then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
        else ⊤) ≤ firstUpperPassage X s ω := by sorry
