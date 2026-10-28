-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_measure_le_one
-- name    : MarkovProcess.IsSubMarkovKernel.measure_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:17:52.105047+00:00
-- url     : https://prove2.me/theorems/8cc93c37-4c49-41a5-b55a-e1690df1559b
-- title:
--   Every sub-Markov kernel assigns mass at most one to a measurable set
-- statement:
--   Every sub-Markov kernel assigns mass at most one to a measurable set. This fact follows directly from the uniform total-mass bound defining a sub-Markov kernel. Ported with the original proof from Scott Armstrong's MarkovProcess (Apache-2.0) as a reusable foundation for kernel semigroups and resolvents.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L34-L36

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

theorem MarkovProcess.IsSubMarkovKernel.measure_le_one (hκ : IsSubMarkovKernel κ) (x : α) (s : Set β) : κ x s ≤ 1 := by sorry
