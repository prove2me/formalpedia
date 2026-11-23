-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
-- name    : GlobalTheory.ProjPoint.hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:32.066846+00:00
-- url     : https://prove2.me/theorems/dcadee63-911c-4a83-8102-bb6e9934d6f6
-- title:
--   Proj Point: hom ext
-- statement:
--   The Proj Point construction uses the hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L183-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L183-L196

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

theorem GlobalTheory.ProjPoint.hom_ext (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) {Y : Scheme.{u}}
    {g₁ g₂ : Spec (.of B) ⟶ Y}
    (h : ∀ (C : Type u) [CommRing C] (ψ : B →+* C) (f : A) (n : ℕ), 0 < n → f ∈ 𝒜 n →
      IsUnit (ψ (φ f)) →
      Spec.map (CommRingCat.ofHom ψ) ≫ g₁ = Spec.map (CommRingCat.ofHom ψ) ≫ g₂) : g₁ = g₂ := by sorry
