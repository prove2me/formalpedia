-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_add
-- name    : MarkovProcess.SubMarkovKernelSemigroup.add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:22:40.855355+00:00
-- url     : https://prove2.me/theorems/301029ba-4e30-4591-91bd-d9d5d8e3d967
-- title:
--   Chapman-Kolmogorov composition law for a sub-Markov kernel semigroup
-- statement:
--   Chapman-Kolmogorov composition law for a sub-Markov kernel semigroup. This foundational statement is ported directly from Scott Armstrong's MarkovProcess, with the Lean 4.33.1 proof and Apache-2.0 attribution preserved. It supports semigroup resolvents and stopped processes.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/KernelSemigroup.lean#L81-L83

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem MarkovProcess.SubMarkovKernelSemigroup.add (s t : NNReal) : P (s + t) = (P t).comp (P s) := by sorry
