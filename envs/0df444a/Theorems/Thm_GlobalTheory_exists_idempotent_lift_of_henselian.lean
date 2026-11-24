-- Prove2me | Theorems.Thm_GlobalTheory_exists_idempotent_lift_of_henselian
-- name    : GlobalTheory.exists_idempotent_lift_of_henselian
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:50.384334+00:00
-- url     : https://prove2.me/theorems/3c17c438-3606-40d2-b4cd-5e6d5725987a
-- title:
--   Global Theory: exists idempotent lift of henselian
-- statement:
--   The Global Theory construction uses the exists idempotent lift of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L197-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L197-L208

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

theorem GlobalTheory.exists_idempotent_lift_of_henselian (R : Type*) {S C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [CommRing C]
    (π : S →+* C) (hπ : Function.Surjective π) {c : C} (hc : IsIdempotentElem c) :
    ∃ e : S, IsIdempotentElem e ∧ π e = c := by sorry
