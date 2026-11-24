-- Prove2me | Theorems.Thm_GlobalTheory_SS_ModelPoints_points_model
-- name    : GlobalTheory.SS.ModelPoints.points_model
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:29.130088+00:00
-- url     : https://prove2.me/theorems/a785ff75-32d7-4826-a7f2-abf6d6dc5d24
-- title:
--   Model Points: points model
-- statement:
--   The Model Points construction uses the points model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpSchemePointsModelOverField.lean#L65-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpSchemePointsModelOverField.lean#L65-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpSchemePointsModelOverField
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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ModelPoints

theorem GlobalTheory.SS.ModelPoints.points_model : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by sorry
