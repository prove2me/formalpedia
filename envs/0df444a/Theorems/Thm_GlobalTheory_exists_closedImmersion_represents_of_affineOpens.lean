-- Prove2me | Theorems.Thm_GlobalTheory_exists_closedImmersion_represents_of_affineOpens
-- name    : GlobalTheory.exists_closedImmersion_represents_of_affineOpens
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:51.735385+00:00
-- url     : https://prove2.me/theorems/479cddc5-7216-484a-86f0-475b0725129e
-- title:
--   Global Theory: exists closed Immersion represents of affine Opens
-- statement:
--   The Global Theory construction uses the exists closed Immersion represents of affine Opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsClosedImmersionRepresentsOfAffineOpens.lean#L11-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsClosedImmersionRepresentsOfAffineOpens.lean#L11-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WhiskerLeftLeftIsPullbackSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFactorClosedImmersionOfLocallyOnSourceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsClosedImmersionRepresentsOfAffineOpens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_closedImmersion_represents_of_affineOpens : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by sorry
