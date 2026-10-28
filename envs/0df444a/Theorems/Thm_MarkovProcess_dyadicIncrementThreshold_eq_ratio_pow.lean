-- Prove2me | Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_eq_ratio_pow
-- name    : MarkovProcess.dyadicIncrementThreshold_eq_ratio_pow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:14:11.506579+00:00
-- url     : https://prove2.me/theorems/f6d44c5d-3b2a-4b74-b767-f7c54fd4ca32
-- title:
--   Dyadic increment threshold equals a geometric power
-- statement:
--   The dyadic level-n increment threshold is the nth power of the one-level threshold decay ratio.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L202-L210

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem MarkovProcess.dyadicIncrementThreshold_eq_ratio_pow (γ : ℝ) (n : ℕ) :
    dyadicIncrementThreshold γ n = dyadicIncrementThresholdRatio γ ^ n := by sorry
