-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_surjective_cotangent_of_residue
-- name    : GlobalTheory.flat_of_surjective_cotangent_of_residue
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:55.755627+00:00
-- url     : https://prove2.me/theorems/cc07609d-94d0-4b5b-af34-c76e8d8732a9
-- title:
--   Global Theory: flat of surjective cotangent of residue
-- statement:
--   The Global Theory construction uses the flat of surjective cotangent of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L428-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L428-L437

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

theorem GlobalTheory.flat_of_surjective_cotangent_of_residue {k : Type*} [CommRing k] [Algebra k A]
    [IsLocalRing A] (hk : Function.Surjective (algebraMap k (ResidueField A))) (φ : A →ₐ[k] A)
    (hle : maximalIdeal A ≤ (maximalIdeal A).comap φ)
    (h₁ : Function.Surjective (Ideal.mapCotangent _ _ φ hle)) : (φ : A →+* A).Flat := by sorry
