-- Prove2me | Theorems.Thm_MarkovProcess_sub_unitDyadicFloorValue_le
-- name    : MarkovProcess.sub_unitDyadicFloorValue_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:49:25.288854+00:00
-- url     : https://prove2.me/theorems/52a826ed-626b-4df4-ad0c-72a49ae0008d
-- title:
--   The gap from `t` to its level-`n` left approximation is at most one dyadic cell
-- statement:
--   The gap from `t` to its level-`n` left approximation is at most one dyadic cell.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicFloor.lean#L67-L83

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

theorem MarkovProcess.sub_unitDyadicFloorValue_le (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    t.1 - (unitDyadicFloorValue n t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by sorry
