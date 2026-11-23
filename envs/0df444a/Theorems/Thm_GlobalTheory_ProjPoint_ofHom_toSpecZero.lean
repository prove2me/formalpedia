-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_ofHom_toSpecZero
-- name    : GlobalTheory.ProjPoint.ofHom_toSpecZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:33.437499+00:00
-- url     : https://prove2.me/theorems/48ed7b77-18f0-4230-b94c-dc77b2cccec4
-- title:
--   Proj Point: of Hom to Spec Zero
-- statement:
--   The Proj Point construction uses the of Hom to Spec Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L119-L125

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

theorem GlobalTheory.ProjPoint.ofHom_toSpecZero (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) :
    ofHom 𝒜 φ hφ ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (𝒜 0) A))) := by sorry
