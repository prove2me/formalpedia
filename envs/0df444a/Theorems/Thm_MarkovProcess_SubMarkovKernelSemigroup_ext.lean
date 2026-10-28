-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_ext
-- name    : MarkovProcess.SubMarkovKernelSemigroup.ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:21:51.486134+00:00
-- url     : https://prove2.me/theorems/eb6c8384-6013-493e-869f-d2ac84e5b14a
-- title:
--   Extensionality of sub-Markov kernel semigroups
-- statement:
--   Two jointly measurable sub-Markov transition-kernel semigroups on the same measurable state space are equal if their transition kernels coincide at every nonnegative time. This extensionality theorem is a structural property of Scott Armstrong's MarkovProcess transition semigroup type.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/KernelSemigroup.lean#L54-L63

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]

@[ext]
theorem MarkovProcess.SubMarkovKernelSemigroup.ext {P Q : SubMarkovKernelSemigroup α}
    (h : ∀ t, P t = Q t) : P = Q := by sorry
