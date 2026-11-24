-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_of_isUnit_mk_of_le_jacobson
-- name    : GlobalTheory.isUnit_of_isUnit_mk_of_le_jacobson
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:04.317629+00:00
-- url     : https://prove2.me/theorems/63495a04-8d7d-4323-a1c0-50352118de26
-- title:
--   Global Theory: is Unit of is Unit mk of le jacobson
-- statement:
--   The Global Theory construction uses the is Unit of is Unit mk of le jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L19-L22

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

theorem GlobalTheory.isUnit_of_isUnit_mk_of_le_jacobson {S : Type*} [CommRing S] {J : Ideal S}
    (hJ : J ≤ (⊥ : Ideal S).jacobson) {x : S} (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by sorry
