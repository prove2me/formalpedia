-- Prove2me | Theorems.Thm_MarkovProcess_unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow
-- name    : MarkovProcess.unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:49:26.802136+00:00
-- url     : https://prove2.me/theorems/947a750f-eb28-4abf-8c55-52c6230d3b87
-- title:
--   Two ordered times separated by at most one level-`n` cell have floor indices separated by at most one
-- statement:
--   Two ordered times separated by at most one level-`n` cell have floor indices separated by
--   at most one.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicFloor.lean#L125-L152

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

theorem MarkovProcess.unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow
    (n : ℕ) {s t : Set.Icc (0 : ℝ) 1} (hst : s.1 ≤ t.1)
    (hgap : t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹) :
    (unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val ≤ 1 := by sorry
