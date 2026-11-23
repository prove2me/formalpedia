-- Prove2me | Theorems.Thm_GlobalTheory_ProjPoint_eq_awayLift
-- name    : GlobalTheory.ProjPoint.eq_awayLift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:27.386803+00:00
-- url     : https://prove2.me/theorems/a4754a98-12cb-4c10-b951-82d449e43052
-- title:
--   Proj Point: eq away Lift
-- statement:
--   The Proj Point construction uses the eq away Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L87-L93

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

theorem GlobalTheory.ProjPoint.eq_awayLift (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (g : Away 𝒜 f →+* B)
    (hg : ∀ n a ha, g (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a) : g = awayLift 𝒜 φ f hf := by sorry
