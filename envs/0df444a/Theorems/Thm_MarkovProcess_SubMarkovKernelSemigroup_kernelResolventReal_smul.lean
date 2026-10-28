-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_kernelResolventReal_smul
-- name    : MarkovProcess.SubMarkovKernelSemigroup.kernelResolventReal_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:43:21.640618+00:00
-- url     : https://prove2.me/theorems/d622964a-7c57-4355-b5f7-a1407f1879f9
-- title:
--   kernelResolventReal smul
-- statement:
--   Exact analytic identity or estimate from Scott Armstrong, MarkovProcess (Apache-2.0). The original theorem is made a reusable public result with the same hypotheses and conclusion. This supports bounds and linearity of time-Laplace kernel resolvents.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Resolvent.lean#L112-L132

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

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.kernelResolventReal_smul (P : SubMarkovKernelSemigroup alpha)
    (lam a : ℝ) (f : alpha → ℝ) :
    P.kernelResolventReal lam (a • f) = a • P.kernelResolventReal lam f := by sorry
