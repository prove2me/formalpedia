-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_norm_kernelIntegral_le_of_bound
-- name    : MarkovProcess.SubMarkovKernelSemigroup.norm_kernelIntegral_le_of_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:43:18.225993+00:00
-- url     : https://prove2.me/theorems/6de6d7bb-6522-4e43-9be6-53bd0a8df57c
-- title:
--   norm kernelIntegral le of bound
-- statement:
--   Exact analytic identity or estimate from Scott Armstrong, MarkovProcess (Apache-2.0). The original theorem is made a reusable public result with the same hypotheses and conclusion. This supports bounds and linearity of time-Laplace kernel resolvents.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Resolvent.lean#L42-L58

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
import Theorems.Thm_MarkovProcess_IsSubMarkovKernel_measure_le_one

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.norm_kernelIntegral_le_of_bound (P : SubMarkovKernelSemigroup alpha)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    |kernelIntegral (P t) f x| ≤ D := by sorry
