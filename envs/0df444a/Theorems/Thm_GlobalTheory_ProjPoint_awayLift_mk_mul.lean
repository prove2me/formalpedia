-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_awayLift_mk_mul
-- name    : GlobalTheory.ProjPoint.awayLift_mk_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:55:25.210208+00:00
-- url     : https://prove2.me/theorems/64cf1ca2-939f-4bfb-ac4f-ff1453b8b73f
-- title:
--   Proj Point: away Lift mk mul
-- statement:
--   The Proj Point construction uses the away Lift mk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L77-L85

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

theorem GlobalTheory.ProjPoint.awayLift_mk_mul (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift 𝒜 φ f hf (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a := by sorry
