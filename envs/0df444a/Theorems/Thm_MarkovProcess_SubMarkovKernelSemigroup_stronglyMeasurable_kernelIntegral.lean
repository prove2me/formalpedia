-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_kernelIntegral
-- name    : MarkovProcess.SubMarkovKernelSemigroup.stronglyMeasurable_kernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:42:03.45087+00:00
-- url     : https://prove2.me/theorems/e8498458-a1d4-4590-8bd4-cfe0a66cb3b1
-- title:
--   stronglyMeasurable kernelIntegral
-- statement:
--   Source theorem stronglyMeasurable_kernelIntegral on the joint time-state kernel and measurability of its kernel integral, from Scott Armstrong, MarkovProcess, Apache-2.0. Original proof retained.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Operator.lean#L40-L44

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem MarkovProcess.SubMarkovKernelSemigroup.stronglyMeasurable_kernelIntegral {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 := by sorry
