-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_ofHom_map
-- name    : GlobalTheory.ProjPoint.ofHom_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:08.467286+00:00
-- url     : https://prove2.me/theorems/088909b0-e1e7-4d07-aa09-4e1ed4b4f9be
-- title:
--   Proj Point: of Hom map
-- statement:
--   The Proj Point construction uses the of Hom map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L235-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L235-L248

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
variable {A' τ τ' : Type u} {A₀ : Type u} [CommRing A₀] [CommRing A'] [SetLike τ A₀]
  [AddSubgroupClass τ A₀] [SetLike τ' A'] [AddSubgroupClass τ' A']
  {𝒜₀ : ℕ → τ} {ℬ : ℕ → τ'} [GradedRing 𝒜₀] [GradedRing ℬ]

theorem GlobalTheory.ProjPoint.ofHom_map (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    (φ : A' →+* B) (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    ofHom ℬ φ hφ ≫ Proj.map g hg =
      ofHom 𝒜₀ (φ.comp g.toRingHom) (map_irrelevant_comp_graded g hg hφ) := by sorry
