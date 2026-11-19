-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfEqualContinuousPublic
-- name    : Kyprianou.Ch01.rationalStrictUpperPassageInfEqualContinuousPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:25:33.658202+00:00
-- url     : https://prove2.me/theorems/adf18101-96bb-4105-8364-810bfe39535d
-- title:
--   Continuous strict first upper passage equals the rational observation infimum
-- statement:
--   For every continuous real path indexed by nonnegative time, the first positive-time strict upper crossing of level s, including infinity when there is no crossing, equals the infimum of all positive rational observation times at which the path exceeds s. This uses the density of positive rationals and continuity of strict exceedance neighbourhoods and remains valid when first passage equals zero or infinity.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), continuous sample paths and rational approximations. Related Proved firstUpperPassage_le_iff_rationalApproachingCrossings.

import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalStrictUpperPassageInfEqualContinuousPublic
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω)) :
    firstUpperPassage X s ω =
      ⨅ r : ℚ,
        if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
          then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
          else ⊤ := by sorry
