-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_of_isMarkovKernel
-- name    : MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:36:43.630698+00:00
-- url     : https://prove2.me/theorems/0ec8e17b-f467-4b63-9f9c-b329f1533edf
-- title:
--   Every Markov kernel is sub-Markov
-- statement:
--   Every Markov kernel is sub-Markov. Source-faithful theorem from Scott Armstrong, MarkovProcess (Apache-2.0); its original proof is staged for Prove2Me remote verification.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L59-L62

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

theorem MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel (κ : Kernel α β) [IsMarkovKernel κ] : IsSubMarkovKernel κ := by sorry
