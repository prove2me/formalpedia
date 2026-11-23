-- Prove2me | Theorems.Thm_GlobalTheory_ProjFrac_map_app_frac
-- name    : GlobalTheory.ProjFrac.map_app_frac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:19.986993+00:00
-- url     : https://prove2.me/theorems/662b7b60-ed2d-4003-9f37-0f652090b8f5
-- title:
--   Proj Frac: map app frac
-- statement:
--   The Proj Frac construction uses the map app frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L238-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L238-L245

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory GlobalTheory.ProjFrac
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {𝒜}
variable {B τ : Type} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)

theorem GlobalTheory.ProjFrac.map_app_frac (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) :
    ((Proj.map φ hφ).app U).hom (frac 𝒜 U a b ha hb hU) =
      frac ℬ (Proj.map φ hφ ⁻¹ᵁ U) (φ a) (φ b) (φ.2 ha) (φ.2 hb) (fun _ hx => hU hx) := by sorry
