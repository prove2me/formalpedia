-- Prove2me | Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_ne_zero
-- name    : MarkovProcess.dyadicIncrementThreshold_ne_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:14:06.323632+00:00
-- url     : https://prove2.me/theorems/beeeffc2-66b6-4d70-b1fc-c3dcd69b63c6
-- title:
--   A positive dyadic threshold is never zero
-- statement:
--   For any strictly positive Hölder exponent, the threshold at every dyadic level is nonzero in the extended nonnegative real numbers.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L69-L74

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

theorem MarkovProcess.dyadicIncrementThreshold_ne_zero {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ 0 := by sorry
