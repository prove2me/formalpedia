-- Prove2me | Theorems.Thm_GlobalTheory_SubmodulePowSimple_mem_span_equivValues
-- name    : GlobalTheory.SubmodulePowSimple.mem_span_equivValues
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:26.590155+00:00
-- url     : https://prove2.me/theorems/43afcfee-8877-482d-a6d0-1b1ab5299d9a
-- title:
--   Submodule Pow Simple: mem span equiv Values
-- statement:
--   The Submodule Pow Simple construction uses the mem span equiv Values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L32-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L32-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.SubmodulePowSimple
variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}

theorem GlobalTheory.SubmodulePowSimple.mem_span_equivValues (a : ι → Module.End ℂ P)
    (hs : ∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) :
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, y ∈ span ℂ (equivValues a m N) := by sorry
