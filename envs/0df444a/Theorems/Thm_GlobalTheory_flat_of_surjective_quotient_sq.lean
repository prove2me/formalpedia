-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_surjective_quotient_sq
-- name    : GlobalTheory.flat_of_surjective_quotient_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:12.532332+00:00
-- url     : https://prove2.me/theorems/519fe18b-fab9-4911-9acd-e2f479e0c118
-- title:
--   Global Theory: flat of surjective quotient sq
-- statement:
--   The Global Theory construction uses the flat of surjective quotient sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L394-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L394-L403

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

theorem GlobalTheory.flat_of_surjective_quotient_sq (hI : I ≤ Ideal.jacobson ⊥) (hle : I ≤ I.comap φ)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ I) (h₁ : ∀ y ∈ I, ∃ x ∈ I, φ x - y ∈ I ^ 2) : φ.Flat := by sorry
