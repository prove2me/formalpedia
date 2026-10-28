-- Prove2me | Theorems.Thm_MarkovProcess_dyadicIncrementDecayRatio_lt_one
-- name    : MarkovProcess.dyadicIncrementDecayRatio_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:14:11.808396+00:00
-- url     : https://prove2.me/theorems/20251240-8315-472d-b0ae-668cdf6c822d
-- title:
--   The dyadic Kolmogorov decay ratio is below one for admissible exponents
-- statement:
--   The inequality for the admissible Hölder exponent makes the geometric bad-event decay ratio strictly less than one.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L33-L41

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

theorem MarkovProcess.dyadicIncrementDecayRatio_lt_one {p q γ : ℝ} (hp : 0 < p)
    (hγ : γ < (q - 1) / p) : dyadicIncrementDecayRatio p q γ < 1 := by sorry
