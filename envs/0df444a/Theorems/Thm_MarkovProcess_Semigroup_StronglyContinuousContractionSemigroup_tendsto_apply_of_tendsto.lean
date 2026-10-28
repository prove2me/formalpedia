-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_tendsto_apply_of_tendsto
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_apply_of_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:47:30.95901+00:00
-- url     : https://prove2.me/theorems/04ae5b7f-b56c-43a6-b595-cf6c84e40123
-- title:
--   Joint continuity of contraction semigroup actions
-- statement:
--   A strongly continuous contraction semigroup acts continuously when both time and the vector
--   vary.  Strong continuity alone only states this for a fixed vector; contractivity makes the
--   dependence on the vector uniform in time.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/FiniteTimeKernelContinuity.lean#L30-L54

import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
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



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_apply_of_tendsto
    (S : StronglyContinuousContractionSemigroup E) {X : Type*} {l : Filter X}
    {t : X → NNReal} {t₀ : NNReal} {f : X → E} {f₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) :
    Tendsto (fun x ↦ S (t x) (f x)) l (nhds (S t₀ f₀)) := by sorry
