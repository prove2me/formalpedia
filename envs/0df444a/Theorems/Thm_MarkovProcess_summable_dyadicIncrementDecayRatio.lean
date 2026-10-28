-- Prove2me | Theorems.Thm_MarkovProcess_summable_dyadicIncrementDecayRatio
-- name    : MarkovProcess.summable_dyadicIncrementDecayRatio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:22:36.201751+00:00
-- url     : https://prove2.me/theorems/cbefbd2e-2dc8-436b-b045-e38665d8baa6
-- title:
--   Geometric summability of Kolmogorov dyadic bad-event majorants
-- statement:
--   The weighted geometric sequence of dyadic increment decay ratios is summable whenever the Kolmogorov exponent inequality makes that ratio smaller than one.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L42-L47

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
import Theorems.Thm_MarkovProcess_dyadicIncrementDecayRatio_lt_one
open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem MarkovProcess.summable_dyadicIncrementDecayRatio {p q γ : ℝ} (M : ℝ≥0) (hp : 0 < p)
    (hγ : γ < (q - 1) / p) :
    Summable (fun n : ℕ ↦ M * dyadicIncrementDecayRatio p q γ ^ n) := by sorry
