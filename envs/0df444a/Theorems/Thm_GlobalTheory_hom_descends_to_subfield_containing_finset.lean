-- Prove2me | Theorems.Thm_GlobalTheory_hom_descends_to_subfield_containing_finset
-- name    : GlobalTheory.hom_descends_to_subfield_containing_finset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:54.40383+00:00
-- url     : https://prove2.me/theorems/c4e9b476-55e9-406e-90f4-a1d4a4f80f05
-- title:
--   Global Theory: hom descends to subfield containing finset
-- statement:
--   The Global Theory construction uses the hom descends to subfield containing finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomDescendsToSubfieldContainingFinset.lean#L36-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomDescendsToSubfieldContainingFinset.lean#L36-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

theorem GlobalTheory.hom_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (X₀ Y₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → IsPullback ψ Y.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by sorry
