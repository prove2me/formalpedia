-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_lintegral_add
-- name    : MarkovProcess.SubMarkovKernelSemigroup.lintegral_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:28:06.570901+00:00
-- url     : https://prove2.me/theorems/6e7a88b4-db48-42a7-8340-2460ce5dc86b
-- title:
--   Chapman-Kolmogorov tower law for nonnegative measurable functions
-- statement:
--   Chapman-Kolmogorov tower law for nonnegative measurable functions. This foundational statement is ported directly from Scott Armstrong's MarkovProcess, with the Lean 4.33.1 proof and Apache-2.0 attribution preserved. It supports semigroup resolvents and stopped processes.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/KernelSemigroup.lean#L99-L103

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

theorem MarkovProcess.SubMarkovKernelSemigroup.lintegral_add (s t : NNReal) (x : α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂P (s + t) x = ∫⁻ y, ∫⁻ z, f z ∂P t y ∂P s x := by sorry
