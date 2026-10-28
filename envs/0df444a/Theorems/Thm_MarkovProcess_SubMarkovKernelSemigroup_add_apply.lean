-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_add_apply
-- name    : MarkovProcess.SubMarkovKernelSemigroup.add_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:29:17.887149+00:00
-- url     : https://prove2.me/theorems/b9988232-febf-4fc1-83f4-df6a1147d0f4
-- title:
--   Chapman-Kolmogorov composition formula for transition measures
-- statement:
--   For a sub-Markov kernel semigroup P and nonnegative times s,t, the transition measure P(s+t)x is the bind of P(s)x with the kernel P(t). It follows from the semigroup addition theorem and Mathlib's kernel-composition evaluation identity. Source: Scott Armstrong, MarkovProcess (Apache-2.0), exact Lean 4.33.1 proof.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/KernelSemigroup.lean#L89-L92

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_add

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem MarkovProcess.SubMarkovKernelSemigroup.add_apply (s t : NNReal) (x : α) :
    P (s + t) x = (P s x).bind (P t) := by sorry
