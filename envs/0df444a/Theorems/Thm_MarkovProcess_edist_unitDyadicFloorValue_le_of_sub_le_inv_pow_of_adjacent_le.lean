-- Prove2me | Theorems.Thm_MarkovProcess_edist_unitDyadicFloorValue_le_of_sub_le_inv_pow_of_adjacent_le
-- name    : MarkovProcess.edist_unitDyadicFloorValue_le_of_sub_le_inv_pow_of_adjacent_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:16:29.17946+00:00
-- url     : https://prove2.me/theorems/ed7dc972-cbdf-446a-909e-369f29dde78c
-- title:
--   Increment bound for nearby dyadic floor samples
-- statement:
--   Adjacent-increment control on level `n` controls the process increment between two ordered
--   times lying at most one level-`n` cell apart.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicFloor.lean#L154-L181

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

theorem MarkovProcess.edist_unitDyadicFloorValue_le_of_sub_le_inv_pow_of_adjacent_le
    {Ω E : Type*} [PseudoEMetricSpace E] {X : NNRat → Ω → E}
    {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ n),
      edist (X (unitDyadicGrid n k.castSucc) ω)
          (X (unitDyadicGrid n k.succ) ω) ≤ ε)
    {s t : Set.Icc (0 : ℝ) 1} (hst : s.1 ≤ t.1)
    (hgap : t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹) :
    edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤ ε := by sorry
