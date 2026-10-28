-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_jointKernel_apply
-- name    : MarkovProcess.SubMarkovKernelSemigroup.jointKernel_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:41:59.088634+00:00
-- url     : https://prove2.me/theorems/47e69419-8c38-49b4-8a15-3e2c56c1f260
-- title:
--   jointKernel apply
-- statement:
--   Source theorem jointKernel_apply on the joint time-state kernel and measurability of its kernel integral, from Scott Armstrong, MarkovProcess, Apache-2.0. Original proof retained.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Operator.lean#L36-L38

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

theorem MarkovProcess.SubMarkovKernelSemigroup.jointKernel_apply (p : NNReal × α) : P.jointKernel p = P p.1 p.2 := by sorry
