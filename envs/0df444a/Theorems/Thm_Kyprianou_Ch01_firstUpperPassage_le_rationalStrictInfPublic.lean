-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_rationalStrictInfPublic
-- name    : Kyprianou.Ch01.firstUpperPassage_le_rationalStrictInfPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:37:01.214104+00:00
-- url     : https://prove2.me/theorems/c3a9c6c8-4b81-431d-b953-0890113f3cf5
-- title:
--   First strict upper passage precedes the rational-observation first-crossing infimum
-- statement:
--   For any real path, the first positive-time strict upper crossing over all nonnegative observation times is at or before the infimum of its positive rational strict crossing times, with infinity for absent crossings. This deterministic order inequality does not require continuity and is one half of the source-faithful rational-grid equality.
-- source:
--   Kyprianou (2006), Chapter 1 first passage approximation, Exercise 1.10(ii).

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_le_rationalStrictInfPublic
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) :
    firstUpperPassage X s ω ≤
      ⨅ r : ℚ,
        if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
          then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
          else ⊤ := by sorry
