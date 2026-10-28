-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_norm_kernelResolventReal_le
-- name    : MarkovProcess.SubMarkovKernelSemigroup.norm_kernelResolventReal_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:46:32.644534+00:00
-- url     : https://prove2.me/theorems/04e4b03b-20de-4d55-8bb6-d0f8c37ba77b
-- title:
--   norm kernelResolventReal le
-- statement:
--   Source-faithful real-kernel resolvent theorem from Scott Armstrong, MarkovProcess (Apache-2.0). It controls bounded observable integrability, resolvent additivity or an explicit positive-shift norm bound, as expressed by the original Lean statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Resolvent.lean#L135-L155

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

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.norm_kernelResolventReal_le (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |P.kernelResolventReal lam f x| ≤ D / lam := by sorry
