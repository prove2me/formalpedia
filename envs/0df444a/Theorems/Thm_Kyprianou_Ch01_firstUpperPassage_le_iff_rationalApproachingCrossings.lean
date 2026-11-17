-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_iff_rationalApproachingCrossings
-- name    : Kyprianou.Ch01.firstUpperPassage_le_iff_rationalApproachingCrossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T22:05:41.154232+00:00
-- url     : https://prove2.me/theorems/eb134ddd-3a20-4a4f-b90c-18be6da4cd60
-- title:
--   Continuous first upper passage by a horizon is characterised by rational strict crossings in every positive extension
-- statement:
--   For a continuous real sample path X, the first strict upper-passage time is at most t exactly when every positive extended horizon t+epsilon contains a strict barrier crossing at a positive rational observation time. The deterministic infimum equivalence firstUpperPassage_le_iff_approachingCrossings produces a real crossing before t+epsilon/2. The open-path rational-witness theorem then places a rational crossing before t+epsilon. Conversely, a positive rational crossing before t+epsilon defines a genuine NNReal crossing at that time, giving the infimum inequality. This bridge reduces the uncountable stopping-time event to a countable rational observation formula and retains the top/infinite passage convention.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6, continuous first-passage stopping-time identity.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_le_iff_rationalApproachingCrossings
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t : ℝ≥0) :
    Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0) ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ((t + ε : ℝ≥0) : ℝ) ∧
          s < X (Real.toNNReal (q : ℝ)) ω := by sorry
