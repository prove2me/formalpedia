-- Prove2me | Theorems.Thm_MarkovProcess_dyadicIncrementThresholdRatio_lt_one
-- name    : MarkovProcess.dyadicIncrementThresholdRatio_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:14:07.652596+00:00
-- url     : https://prove2.me/theorems/e46ebb5d-36ee-485c-9aa5-8262981dc3bb
-- title:
--   Positive Hölder exponents give a threshold ratio strictly below one
-- statement:
--   For positive Hölder exponent gamma, the geometric ratio of consecutive dyadic thresholds is strictly less than one.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L211-L216

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

theorem MarkovProcess.dyadicIncrementThresholdRatio_lt_one {γ : ℝ} (hγ : 0 < γ) :
    dyadicIncrementThresholdRatio γ < 1 := by sorry
