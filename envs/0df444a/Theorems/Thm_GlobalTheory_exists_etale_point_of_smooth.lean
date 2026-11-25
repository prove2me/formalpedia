-- Prove2me | Theorems.Thm_GlobalTheory_exists_etale_point_of_smooth
-- name    : GlobalTheory.exists_etale_point_of_smooth
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:57.925333+00:00
-- url     : https://prove2.me/theorems/df3b0080-4000-4768-a226-8ef14d3d314a
-- title:
--   Global Theory: exists etale point of smooth
-- statement:
--   The Global Theory construction uses the exists etale point of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L205-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L205-L252

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
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

theorem GlobalTheory.exists_etale_point_of_smooth (B : Type u) [CommRing B] [IsLocalRing B]
    (K : Type*) [Field K] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K] [IsSepClosed K]
    (s : Spec (.of B) ⟶ S) (O : X.Opens) (hO : ∃ x ∈ O, f x = s (closedPoint B)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (_ : W →ₐ[B] K)
      (y : Spec (.of W) ⟶ X),
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B W)) ≫ s ∧ Set.range y ⊆ O := by sorry
