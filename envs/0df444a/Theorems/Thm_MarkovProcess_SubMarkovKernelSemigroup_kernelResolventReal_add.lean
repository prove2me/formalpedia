-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_kernelResolventReal_add
-- name    : MarkovProcess.SubMarkovKernelSemigroup.kernelResolventReal_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:51:01.656618+00:00
-- url     : https://prove2.me/theorems/39e77fb1-fcc2-4fd2-8607-e75dc2c197f3
-- title:
--   kernelResolventReal add
-- statement:
--   Source-faithful real-kernel resolvent theorem from Scott Armstrong, MarkovProcess (Apache-2.0). It controls bounded observable integrability, resolvent additivity or an explicit positive-shift norm bound, as expressed by the original Lean statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Resolvent.lean#L75-L111

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_integrableOn_kernelResolventReal_integrand

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.kernelResolventReal_add (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    P.kernelResolventReal lam (f + g) =
      P.kernelResolventReal lam f + P.kernelResolventReal lam g := by sorry
