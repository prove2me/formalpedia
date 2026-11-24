-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_SpecMap_ofHom
-- name    : GlobalTheory.ProjPoint.SpecMap_ofHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:47.015425+00:00
-- url     : https://prove2.me/theorems/fb4e5655-2115-4794-abe2-a36405cd83a0
-- title:
--   Proj Point: Spec Map of Hom
-- statement:
--   The Proj Point construction uses the Spec Map of Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L199-L204

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

theorem GlobalTheory.ProjPoint.SpecMap_ofHom (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      ofHom 𝒜 (ψ.comp φ) (map_irrelevant_comp 𝒜 hφ ψ) := by sorry
