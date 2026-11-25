-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_specializes_lift_pullback_snd_fromSpecStalk
-- name    : GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:53.486594+00:00
-- url     : https://prove2.me/theorems/1d832606-0bb9-531d-91c3-91bdc2e6804a
-- title:
--   T: exists specializes lift pullback snd from Spec Stalk
-- statement:
--   The T construction uses the exists specializes lift pullback snd from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecializesLiftClosedFibreStalkBaseChangeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecializesLiftClosedFibreStalkBaseChangeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecializesLiftClosedFibreStalkBaseChange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecializesLiftClosedFibreStalkBaseChangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by sorry
