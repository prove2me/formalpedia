-- Prove2me | Theorems.Thm_MarkovProcess_IsSubMarkovKernel_comp
-- name    : MarkovProcess.IsSubMarkovKernel.comp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:40:37.338598+00:00
-- url     : https://prove2.me/theorems/1c0309bc-bde9-4b01-b484-08388af32928
-- title:
--   Composition preserves the sub-Markov property
-- statement:
--   For sub-Markov transition kernels kappa and eta, the composed kernel eta ∘ₖ kappa is also sub-Markov. The proof uses the bound on the total mass of a kernel composition and the uniform bounds for the factors. Faithful to Scott Armstrong, MarkovProcess (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/Basic.lean#L64-L72

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel
import Theorems.Thm_MarkovProcess_IsSubMarkovKernel_bound_le_one

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}

theorem MarkovProcess.IsSubMarkovKernel.comp (hη : IsSubMarkovKernel η) (hκ : IsSubMarkovKernel κ) :
    IsSubMarkovKernel (η ∘ₖ κ) := by sorry
