-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Host_mem_Psi_or
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.mem_Psi_or
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:41.980848+00:00
-- url     : https://prove2.me/theorems/7d627a14-8647-5e6a-a29a-a0ee75f47d07
-- title:
--   Host: mem Psi or
-- statement:
--   The Host construction uses the mem Psi or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L58-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
variable (H : Host E)

theorem GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.mem_Psi_or (τ : E →+* ℂ) : τ ∈ H.Psi ∨ (starRingEnd ℂ).comp τ ∈ H.Psi := by sorry
