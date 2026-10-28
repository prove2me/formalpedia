-- Prove2me | Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_unitDyadicGridBadIncrement_threshold_le
-- name    : MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:22:42.797165+00:00
-- url     : https://prove2.me/theorems/f0263457-012f-4931-a97c-e04a0a3b2de6
-- title:
--   Dyadic bad-increment probability bound at Hölder threshold
-- statement:
--   The Kolmogorov moment condition bounds a level-n bad-increment event by M times the nth power of the geometric decay ratio.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L122-L131

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
import Theorems.Thm_MarkovProcess_dyadic_bound_normalization
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_unitDyadicGridBadIncrement_le
import Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_ne_zero
import Theorems.Thm_MarkovProcess_dyadicIncrementThreshold_ne_top
open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_threshold_le
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ) (n : ℕ) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p (dyadicIncrementThreshold γ n)) ≤
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by sorry
