-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_bound_le_one
-- name    : MarkovProcess.IsSubMarkovKernel.bound_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:36:42.458726+00:00
-- url     : https://prove2.me/theorems/9a04d1f8-702d-404d-b049-d27600e25bce
-- title:
--   The uniform mass bound of a sub-Markov kernel is at most one
-- statement:
--   The uniform mass bound of a sub-Markov kernel is at most one. Source-faithful theorem from Scott Armstrong, MarkovProcess (Apache-2.0); its original proof is staged for Prove2Me remote verification.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L38-L41

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

theorem MarkovProcess.IsSubMarkovKernel.bound_le_one (hκ : IsSubMarkovKernel κ) : κ.bound ≤ 1 := by sorry
