-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_of_isUnit_map_of_ker_le_jacobson
-- name    : GlobalTheory.isUnit_of_isUnit_map_of_ker_le_jacobson
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:06.300558+00:00
-- url     : https://prove2.me/theorems/c9d4844f-15e0-4c18-9a0d-13066450a222
-- title:
--   Global Theory: is Unit of is Unit map of ker le jacobson
-- statement:
--   The Global Theory construction uses the is Unit of is Unit map of ker le jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L13-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

theorem GlobalTheory.isUnit_of_isUnit_map_of_ker_le_jacobson (π : B →+* C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π ≤ Ideal.jacobson ⊥) {b : B} (hb : IsUnit (π b)) : IsUnit b := by sorry
