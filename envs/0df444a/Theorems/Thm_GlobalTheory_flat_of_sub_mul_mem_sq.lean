-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_sub_mul_mem_sq
-- name    : GlobalTheory.flat_of_sub_mul_mem_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:59.527982+00:00
-- url     : https://prove2.me/theorems/2c690e20-f222-48be-8a2a-fb9686e755b1
-- title:
--   Global Theory: flat of sub mul mem sq
-- statement:
--   The Global Theory construction uses the flat of sub mul mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L439-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L439-L445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
variable [IsNoetherianRing A] {φ : A →+* A}

theorem GlobalTheory.flat_of_sub_mul_mem_sq [IsLocalRing A] (hle : maximalIdeal A ≤ (maximalIdeal A).comap φ)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) {c : A} (hc : IsUnit c)
    (h₁ : ∀ x ∈ maximalIdeal A, φ x - c * x ∈ maximalIdeal A ^ 2) : φ.Flat := by sorry
