-- Prove2me | Theorems.Thm_GlobalTheory_idempotent_eq_of_forall_isMaximal
-- name    : GlobalTheory.idempotent_eq_of_forall_isMaximal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:55.692946+00:00
-- url     : https://prove2.me/theorems/d30c6b82-9b91-4397-b666-9e587d453881
-- title:
--   Global Theory: idempotent eq of forall is Maximal
-- statement:
--   The Global Theory construction uses the idempotent eq of forall is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L168-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L168-L177

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

theorem GlobalTheory.idempotent_eq_of_forall_isMaximal {S : Type*} [CommRing S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : ∀ n : Ideal S, n.IsMaximal → (a ∈ n ↔ b ∈ n)) : a = b := by sorry
