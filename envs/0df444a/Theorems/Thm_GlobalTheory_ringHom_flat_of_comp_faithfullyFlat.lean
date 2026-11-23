-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_flat_of_comp_faithfullyFlat
-- name    : GlobalTheory.ringHom_flat_of_comp_faithfullyFlat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:07.763992+00:00
-- url     : https://prove2.me/theorems/b0220567-ca60-4467-9fb8-720d3966cd29
-- title:
--   Global Theory: ring Hom flat of comp faithfully Flat
-- statement:
--   The Global Theory construction uses the ring Hom flat of comp faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L453-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L453-L468

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

theorem GlobalTheory.ringHom_flat_of_comp_faithfullyFlat {φ : A →+* B} {β : B →+* B'}
    (hβ : β.FaithfullyFlat) (h : (β.comp φ).Flat) : φ.Flat := by sorry
