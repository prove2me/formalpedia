-- Prove2me | Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_ne_top
-- name    : MarkovProcess.dyadicIncrementThreshold_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:14:10.179123+00:00
-- url     : https://prove2.me/theorems/9706976d-d621-44f4-ab78-36473ae68d0f
-- title:
--   A positive dyadic threshold is always finite
-- statement:
--   For any strictly positive Hölder exponent, the threshold at every dyadic level is never infinite.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L74-L79

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

theorem MarkovProcess.dyadicIncrementThreshold_ne_top {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    dyadicIncrementThreshold γ n ≠ ∞ := by sorry
