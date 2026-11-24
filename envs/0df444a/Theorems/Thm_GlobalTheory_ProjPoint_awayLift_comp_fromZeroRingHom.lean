-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_awayLift_comp_fromZeroRingHom
-- name    : GlobalTheory.ProjPoint.awayLift_comp_fromZeroRingHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:06.729794+00:00
-- url     : https://prove2.me/theorems/b53c8a9b-e978-4d40-9a51-db94b0545849
-- title:
--   Proj Point: away Lift comp from Zero Ring Hom
-- statement:
--   The Proj Point construction uses the away Lift comp from Zero Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L95-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]

theorem GlobalTheory.ProjPoint.awayLift_comp_fromZeroRingHom (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) :
    (awayLift 𝒜 φ f hf).comp (fromZeroRingHom 𝒜 _) = φ.comp (algebraMap (𝒜 0) A) := by sorry
