-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_twoStepProduct_c0
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_twoStepProduct_c0
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:44.53097+00:00
-- url     : https://prove2.me/theorems/302e8cd0-ca65-4f76-bb41-0f3eeadc0722
-- title:
--   MarkovProcess: tendsto_twoStepProduct_c0
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end Semigroup.StronglyContinuousContractionSemigroup

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]





end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_twoStepProduct_c0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X}
    {t s : X → NNReal} {t₀ s₀ : NNReal}
    {f g : X → C₀(alpha, ℝ)} {f₀ g₀ : C₀(alpha, ℝ)}
    (ht : Tendsto t l (nhds t₀)) (hs : Tendsto s l (nhds s₀))
    (hf : Tendsto f l (nhds f₀)) (hg : Tendsto g l (nhds g₀)) (x : alpha) :
    Tendsto
      (fun a ↦ kernelIntegral (P (t a))
        (f a * hP.c0Semigroup (s a) (g a)) x)
      l
      (nhds (kernelIntegral (P t₀)
        (f₀ * hP.c0Semigroup s₀ g₀) x)) := by sorry
