-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_idempotent_lift_of_henselian
-- name    : GlobalTheory.existsUnique_idempotent_lift_of_henselian
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:20.397183+00:00
-- url     : https://prove2.me/theorems/dcfd12aa-22e6-5810-980f-879034cc8876
-- title:
--   Global Theory: exists Unique idempotent lift of henselian
-- statement:
--   The Global Theory construction uses the exists Unique idempotent lift of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L210-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L210-L217

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

theorem GlobalTheory.existsUnique_idempotent_lift_of_henselian (R : Type*) {S C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [CommRing C]
    (π : S →+* C) (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ (⊥ : Ideal S).jacobson)
    {c : C} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ π e = c := by sorry
