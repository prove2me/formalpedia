-- Prove2me | Theorems.Thm_GlobalTheory_quotientMap_pow_surjective
-- name    : GlobalTheory.quotientMap_pow_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:15:27.443206+00:00
-- url     : https://prove2.me/theorems/a7d47fd4-68b4-403b-8d85-5e3362b356ef
-- title:
--   Global Theory: quotient Map pow surjective
-- statement:
--   The Global Theory construction uses the quotient Map pow surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L322-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L322-L340

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

theorem GlobalTheory.quotientMap_pow_surjective (hle : I ≤ J.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ J)
    (h₁ : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ 2) (n : ℕ) :
    Function.Surjective (Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow_of_le hle n)) := by sorry
