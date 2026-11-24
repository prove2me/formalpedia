-- Prove2me | Theorems.Thm_GlobalTheory_mem_jacobson_bot_of_forall_isMaximal
-- name    : GlobalTheory.mem_jacobson_bot_of_forall_isMaximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:06.163798+00:00
-- url     : https://prove2.me/theorems/ce8f3981-364d-4a4a-9028-fc7ff9e3865e
-- title:
--   Global Theory: mem jacobson bot of forall is Maximal
-- statement:
--   The Global Theory construction uses the mem jacobson bot of forall is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L155-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.mem_jacobson_bot_of_forall_isMaximal {S : Type*} [CommRing S] {x : S}
    (h : ∀ n : Ideal S, n.IsMaximal → x ∈ n) : x ∈ (⊥ : Ideal S).jacobson := by sorry
