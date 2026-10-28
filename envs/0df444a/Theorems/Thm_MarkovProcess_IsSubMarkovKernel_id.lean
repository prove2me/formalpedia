-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_id
-- name    : MarkovProcess.IsSubMarkovKernel.id
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:36:42.952816+00:00
-- url     : https://prove2.me/theorems/d0be6cd9-47c8-46af-99d7-6631d56690eb
-- title:
--   The identity transition kernel is sub-Markov
-- statement:
--   The identity transition kernel is sub-Markov. Source-faithful theorem from Scott Armstrong, MarkovProcess (Apache-2.0); its original proof is staged for Prove2Me remote verification.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L53-L57

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

theorem MarkovProcess.IsSubMarkovKernel.id : IsSubMarkovKernel (Kernel.id : Kernel α α) := by sorry
