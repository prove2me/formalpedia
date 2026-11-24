-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_flat_of_square_of_isLocalHom
-- name    : GlobalTheory.ringHom_flat_of_square_of_isLocalHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:09.839839+00:00
-- url     : https://prove2.me/theorems/d184e134-60e8-4930-92e2-1d2dd5990b87
-- title:
--   Global Theory: ring Hom flat of square of is Local Hom
-- statement:
--   The Global Theory construction uses the ring Hom flat of square of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L475-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L475-L481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

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
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

theorem GlobalTheory.ringHom_flat_of_square_of_isLocalHom [IsLocalRing B] [IsLocalRing B'] {φ : A →+* B}
    {φ' : A' →+* B'} {α : A →+* A'} {β : B →+* B'} [IsLocalHom β]
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.Flat) (hφ' : φ'.Flat) : φ.Flat := by sorry
