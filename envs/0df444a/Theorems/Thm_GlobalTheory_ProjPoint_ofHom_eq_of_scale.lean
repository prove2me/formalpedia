-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_ofHom_eq_of_scale
-- name    : GlobalTheory.ProjPoint.ofHom_eq_of_scale
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:05.205592+00:00
-- url     : https://prove2.me/theorems/4517f527-e78a-4612-ace8-1572a475e5d7
-- title:
--   Proj Point: of Hom eq of scale
-- statement:
--   The Proj Point construction uses the of Hom eq of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L206-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L206-L220

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

theorem GlobalTheory.ProjPoint.ofHom_eq_of_scale {φ φ' : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hφ' : (irrelevant 𝒜).toIdeal.map φ' = ⊤) (c : B)
    (hc : ∀ n, ∀ a ∈ 𝒜 n, φ' a = c ^ n * φ a) : ofHom 𝒜 φ' hφ' = ofHom 𝒜 φ hφ := by sorry
