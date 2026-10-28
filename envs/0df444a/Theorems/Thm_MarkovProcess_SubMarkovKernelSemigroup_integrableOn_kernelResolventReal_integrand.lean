-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_integrableOn_kernelResolventReal_integrand
-- name    : MarkovProcess.SubMarkovKernelSemigroup.integrableOn_kernelResolventReal_integrand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:47:01.605845+00:00
-- url     : https://prove2.me/theorems/b41c21dd-8f22-4314-9828-1a2e45a9cf3f
-- title:
--   integrableOn kernelResolventReal integrand
-- statement:
--   Source-faithful real-kernel resolvent theorem from Scott Armstrong, MarkovProcess (Apache-2.0). It controls bounded observable integrability, resolvent additivity or an explicit positive-shift norm bound, as expressed by the original Lean statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Resolvent.lean#L59-L74

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_KernelResolvents
import Theorems.Thm_MarkovProcess_IsSubMarkovKernel_isFiniteKernel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_norm_kernelIntegral_le_of_bound
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_measurable_kernelIntegral

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.integrableOn_kernelResolventReal_integrand
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by sorry
