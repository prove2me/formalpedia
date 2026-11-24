-- Prove2me | Theorems.Thm_GlobalTheory_lift_ext_of_unramified
-- name    : GlobalTheory.lift_ext_of_unramified
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:19.72603+00:00
-- url     : https://prove2.me/theorems/3dac13fd-f1e6-462b-a322-8d067dfee904
-- title:
--   Global Theory: lift ext of unramified
-- statement:
--   The Global Theory construction uses the lift ext of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L101-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L101-L133

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem GlobalTheory.lift_ext_of_unramified [FormallyUnramified f] [LocallyOfFiniteType f]
    {B C : CommRingCat.{u}} (π : B ⟶ C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥) {x₁ x₂ : Spec B ⟶ X}
    (h₀ : Spec.map π ≫ x₁ = Spec.map π ≫ x₂) (h : x₁ ≫ f = x₂ ≫ f) : x₁ = x₂ := by sorry
