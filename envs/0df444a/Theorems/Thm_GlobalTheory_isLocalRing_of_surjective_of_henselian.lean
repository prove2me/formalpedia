-- Prove2me | Theorems.Thm_GlobalTheory_isLocalRing_of_surjective_of_henselian
-- name    : GlobalTheory.isLocalRing_of_surjective_of_henselian
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:38.892009+00:00
-- url     : https://prove2.me/theorems/dd33a675-aac4-4300-b14b-abd0724e85fa
-- title:
--   Global Theory: is Local Ring of surjective of henselian
-- statement:
--   The Global Theory construction uses the is Local Ring of surjective of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L28-L35

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

theorem GlobalTheory.isLocalRing_of_surjective_of_henselian [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (π : B →+* C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) : IsLocalRing C := by sorry
