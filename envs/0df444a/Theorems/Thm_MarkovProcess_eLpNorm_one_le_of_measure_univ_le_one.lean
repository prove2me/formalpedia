-- Prove2me | Theorems.Thm_MarkovProcess_eLpNorm_one_le_of_measure_univ_le_one
-- name    : MarkovProcess.eLpNorm_one_le_of_measure_univ_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:44.427753+00:00
-- url     : https://prove2.me/theorems/7af9c9bb-3f4c-4a80-8188-3b643e66d5b1
-- title:
--   MarkovProcess: eLpNorm_one_le_of_measure_univ_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_LpFinite_cf939c30
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]











end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

open MarkovProcess in

theorem MarkovProcess.eLpNorm_one_le_of_measure_univ_le_one {ν : Measure α} {f : α → ℝ}
    [IsFiniteMeasure ν] {p : NNReal} (hp : 1 ≤ p) (hν : ν Set.univ ≤ 1)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 1 ν ≤ eLpNorm f p ν := by sorry
