-- Prove2me | Theorems.Thm_MarkovProcess_tendsto_dyadicIncrementThreshold_ancestor_tail_zero
-- name    : MarkovProcess.tendsto_dyadicIncrementThreshold_ancestor_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:49:28.852334+00:00
-- url     : https://prove2.me/theorems/076ceb7d-53e8-400c-895a-7f7266632147
-- title:
--   Vanishing tails of dyadic increment thresholds
-- statement:
--   For a positive exponent, the exact infinite threshold-tail bound above level `n`
--   tends to zero as `n` tends to infinity.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicChaining.lean#L322-L341

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/



open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]













open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.tendsto_dyadicIncrementThreshold_ancestor_tail_zero
    {γ : ℝ} (hγ : 0 < γ) :
    Tendsto
      (fun n : ℕ ↦ dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹)
      atTop (nhds 0) := by sorry
