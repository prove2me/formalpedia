-- Prove2me | Theorems.Thm_GlobalTheory_T_local_ring_points_ideal_criterion
-- name    : GlobalTheory.T.local_ring_points_ideal_criterion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:16.84909+00:00
-- url     : https://prove2.me/theorems/2059105e-2b5f-46d6-8eaf-ac3c638014a0
-- title:
--   T: local ring points ideal criterion
-- statement:
--   The T construction uses the local ring points ideal criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalRingPointsIdealCriterionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalRingPointsIdealCriterionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingPointsIdealCriterion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingPointsIdealCriterionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_ring_points_ideal_criterion : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by sorry
