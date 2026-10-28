-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_isFiniteKernel
-- name    : MarkovProcess.IsSubMarkovKernel.isFiniteKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:17:52.476582+00:00
-- url     : https://prove2.me/theorems/ad1e2ff8-f2f3-45d0-9b4c-adf7b6fdb75a
-- title:
--   Every sub-Markov kernel is a finite kernel
-- statement:
--   Every sub-Markov kernel is a finite kernel. This fact follows directly from the uniform total-mass bound defining a sub-Markov kernel. Ported with the original proof from Scott Armstrong's MarkovProcess (Apache-2.0) as a reusable foundation for kernel semigroups and resolvents.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L43-L45

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}

theorem MarkovProcess.IsSubMarkovKernel.isFiniteKernel (hκ : IsSubMarkovKernel κ) : IsFiniteKernel κ := by sorry
