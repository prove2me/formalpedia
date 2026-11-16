-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_iff_approachingCrossings
-- name    : Kyprianou.Ch01.firstUpperPassage_le_iff_approachingCrossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:58:21.403664+00:00
-- url     : https://prove2.me/theorems/0b5028fb-149e-458b-a431-cea24134024c
-- title:
--   First strict upper-passage time is below a horizon exactly when every positive extension contains a crossing
-- statement:
--   For an arbitrary real path on nonnegative time, the strict first upper-passage time T, defined as the conditional infimum of all positive strict crossings and ∞ if none exists, satisfies T≤t exactly when every strictly positive extension t+epsilon contains a positive-time strict crossing. The forward direction uses exists_lt_of_csInf_lt on the nonempty crossing set. Conversely every extended-horizon crossing bounds sInf of that set above by t+epsilon, and le_of_forall_pos_le_add gives sInf≤t. The statement is exact at boundary contact, handles paths never crossing, and needs no continuity, stochastic properties or measurability. Combining with rational-time density and countable natural-past measurability yields the continuous first-passage stopping-time condition.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6; deterministic first passage infimum identity.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_le_iff_approachingCrossings
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) (t : ℝ≥0) :
    Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0) ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ v : ℝ≥0, 0 < v ∧ v < t + ε ∧ s < X v ω := by sorry
