-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_measurable_kernelIntegral
-- name    : MarkovProcess.SubMarkovKernelSemigroup.measurable_kernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:44:23.764639+00:00
-- url     : https://prove2.me/theorems/acd13eba-6604-4dfc-a065-ad842516c5e7
-- title:
--   measurable kernelIntegral
-- statement:
--   Source theorem measurable_kernelIntegral on the joint time-state kernel and measurability of its kernel integral, from Scott Armstrong, MarkovProcess, Apache-2.0. Original proof retained.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Operator.lean#L46-L49

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_JointKernel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_kernelIntegral

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem MarkovProcess.SubMarkovKernelSemigroup.measurable_kernelIntegral {f : α → ℝ} (hf : Measurable f) :
    Measurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 := by sorry
