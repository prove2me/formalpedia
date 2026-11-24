-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_ofHom_preimage_basicOpen
-- name    : GlobalTheory.ProjPoint.ofHom_preimage_basicOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:03.332016+00:00
-- url     : https://prove2.me/theorems/5715f077-eff9-4b2f-9290-d104ecc98757
-- title:
--   Proj Point: of Hom preimage basic Open
-- statement:
--   The Proj Point construction uses the of Hom preimage basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L112-L116

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

theorem GlobalTheory.ProjPoint.ofHom_preimage_basicOpen (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    ofHom 𝒜 φ hφ ⁻¹ᵁ Proj.basicOpen 𝒜 r = PrimeSpectrum.basicOpen (φ r) := by sorry
