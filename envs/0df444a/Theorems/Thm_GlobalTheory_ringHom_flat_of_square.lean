-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_flat_of_square
-- name    : GlobalTheory.ringHom_flat_of_square
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:19.902513+00:00
-- url     : https://prove2.me/theorems/a578f126-b6c4-4bab-a8d2-9ea6383c30f9
-- title:
--   Global Theory: ring Hom flat of square
-- statement:
--   The Global Theory construction uses the ring Hom flat of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L470-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L470-L473

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

theorem GlobalTheory.ringHom_flat_of_square {φ : A →+* B} {φ' : A' →+* B'} {α : A →+* A'} {β : B →+* B'}
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.FaithfullyFlat) (hφ' : φ'.Flat) :
    φ.Flat := by sorry
