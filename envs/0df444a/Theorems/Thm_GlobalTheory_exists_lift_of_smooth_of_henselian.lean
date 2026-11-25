-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_of_smooth_of_henselian
-- name    : GlobalTheory.exists_lift_of_smooth_of_henselian
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:21.802037+00:00
-- url     : https://prove2.me/theorems/872d54f7-9b68-5068-8b87-4594274c8b67
-- title:
--   Global Theory: exists lift of smooth of henselian
-- statement:
--   The Global Theory construction uses the exists lift of smooth of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L78-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L78-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem GlobalTheory.exists_lift_of_smooth_of_henselian [Smooth f] {B C : CommRingCat.{u}} [IsLocalRing B]
    (π : B ⟶ C) (hπ : Function.Surjective π) [HenselianRing B (RingHom.ker π.hom)]
    (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by sorry
