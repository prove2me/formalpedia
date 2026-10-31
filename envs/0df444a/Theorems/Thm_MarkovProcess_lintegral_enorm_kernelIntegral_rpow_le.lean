-- Prove2me | Theorems.Thm_MarkovProcess_lintegral_enorm_kernelIntegral_rpow_le
-- name    : MarkovProcess.lintegral_enorm_kernelIntegral_rpow_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:08.800997+00:00
-- url     : https://prove2.me/theorems/014141cb-3256-4fc3-931e-b8e41cc025a1
-- title:
--   MarkovProcess: lintegral_enorm_kernelIntegral_rpow_le
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

theorem MarkovProcess.lintegral_enorm_kernelIntegral_rpow_le
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
      ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ := by sorry
