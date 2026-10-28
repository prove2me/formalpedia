-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_zero
-- name    : MarkovProcess.IsSubMarkovKernel.zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:36:42.878975+00:00
-- url     : https://prove2.me/theorems/8cc7eae8-b61a-4306-b896-b361fe68c8f8
-- title:
--   The zero transition kernel is sub-Markov
-- statement:
--   The zero transition kernel is sub-Markov. Source-faithful theorem from Scott Armstrong, MarkovProcess (Apache-2.0); its original proof is staged for Prove2Me remote verification.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L47-L51

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

theorem MarkovProcess.IsSubMarkovKernel.zero : IsSubMarkovKernel (0 : Kernel α β) := by sorry
