-- Prove2me | Theorems.Thm_MarkovProcess_edist_limit_le_dyadicFloorLimitModulus
-- name    : MarkovProcess.edist_limit_le_dyadicFloorLimitModulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:48:40.43255+00:00
-- url     : https://prove2.me/theorems/5e2edc1a-12a4-4219-9a98-b6cf59b26c53
-- title:
--   Distance limits bounded by dyadic ancestor tails
-- statement:
--   A uniform ancestor-tail bound and a same-level comparison bound pass to arbitrary limits of
--   the two floor-sample sequences.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicFloor.lean#L427-L481

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
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
# Dyadic floor approximation and the unit-interval continuous modification

This file merges the following former modules, one section each:

* `DyadicFloorApproximation`: Left dyadic approximations of unit-interval times
* `DyadicFloorPair`: Comparing two dyadic floor approximations
* `DyadicFloorSampleCauchy`: Cauchy control of dyadic floor samples
* `DyadicFloorDenseTime`: Dyadic floor samples at dyadic times
* `DyadicFloorSampleLimit`: Limits of dyadic floor samples
* `DyadicFloorLimitControl`: Uniform control of dyadic floor-sample limits
* `DyadicFloorLimitPath`: The canonical unit-interval dyadic-floor limit path
* `DyadicFloorConvergenceInMeasure`: Convergence in measure of dyadic floor samples
* `DyadicFloorUnitModification`: A continuous modification on the unit interval
-/




noncomputable section


















open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section












open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]










noncomputable section


















open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]





open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.edist_limit_le_dyadicFloorLimitModulus
    {X : NNRat → Ω → E} {γ : ℝ} {n : ℕ} {ω : Ω}
    {s t : Set.Icc (0 : ℝ) 1} {y z : E}
    (htail : ∀ r (u : Set.Icc (0 : ℝ) 1),
      edist (X (unitDyadicFloorValue (n + r) u) ω)
          (X (unitDyadicFloorValue n u) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹)
    (hpair : edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤ dyadicIncrementThreshold γ n)
    (hy : Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m s) ω) atTop (nhds y))
    (hz : Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m t) ω) atTop (nhds z)) :
    edist y z ≤ dyadicFloorLimitModulus γ n := by sorry
