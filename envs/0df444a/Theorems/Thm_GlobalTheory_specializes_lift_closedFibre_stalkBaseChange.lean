-- Prove2me | Theorems.Thm_GlobalTheory_specializes_lift_closedFibre_stalkBaseChange
-- name    : GlobalTheory.specializes_lift_closedFibre_stalkBaseChange
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:38.342518+00:00
-- url     : https://prove2.me/theorems/eb847964-5f17-4bd1-9e53-f183f9e3a570
-- title:
--   Global Theory: specializes lift closed Fibre stalk Base Change
-- statement:
--   The Global Theory construction uses the specializes lift closed Fibre stalk Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecializesLiftClosedFibreStalkBaseChange.lean#L6-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecializesLiftClosedFibreStalkBaseChange.lean#L6-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecializesLiftClosedFibreStalkBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open GlobalTheory

theorem GlobalTheory.specializes_lift_closedFibre_stalkBaseChange : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by sorry
