-- Prove2me | Theorems.Thm_GlobalTheory_quotientMap_pow_bijective
-- name    : GlobalTheory.quotientMap_pow_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:13.223966+00:00
-- url     : https://prove2.me/theorems/f7609465-e94b-4a3b-92b6-ed22acdd9352
-- title:
--   Global Theory: quotient Map pow bijective
-- statement:
--   The Global Theory construction uses the quotient Map pow bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L388-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L388-L392

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

theorem GlobalTheory.quotientMap_pow_bijective (hle : I ≤ I.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ I)
    (h₁ : ∀ y ∈ I, ∃ x ∈ I, φ x - y ∈ I ^ 2) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (I ^ n) φ (pow_le_comap_pow_of_le hle n)) := by sorry
