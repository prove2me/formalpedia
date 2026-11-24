-- Prove2me | Theorems.Thm_GlobalTheory_SS_Translates_val_eq
-- name    : GlobalTheory.SS.Translates.val_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:17:59.321841+00:00
-- url     : https://prove2.me/theorems/cead999c-d7de-4ce9-b3ba-eb8b466660d9
-- title:
--   Translates: val eq
-- statement:
--   The Translates construction uses the val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L18-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L18-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates

theorem GlobalTheory.SS.Translates.val_eq {T X X₁ X₂ O₁ O₂ Y S : Scheme.{0}} (d : T ⟶ X) {z : X} (hz : z ∈ closure (Set.range d))
    (u₁ : X ⟶ X₁) (u₂ : X ⟶ X₂) (i₁ : O₁ ⟶ X₁) (i₂ : O₂ ⟶ X₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (p : O₁ ⟶ Y) (q : O₂ ⟶ Y) (π : Y ⟶ S) [IsSeparated π] (ρ₁ : X₁ ⟶ S) (ρ₂ : X₂ ⟶ S)
    (hp : p ≫ π = i₁ ≫ ρ₁) (hq : q ≫ π = i₂ ≫ ρ₂) (hu : u₁ ≫ ρ₁ = u₂ ≫ ρ₂)
    (h : ∀ (T' : Scheme.{0}) (a : T' ⟶ T) (t₁ : T' ⟶ O₁) (t₂ : T' ⟶ O₂), t₁ ≫ i₁ = a ≫ d ≫ u₁ →
      t₂ ≫ i₂ = a ≫ d ≫ u₂ → t₁ ≫ p = t₂ ≫ q)
    {o₁ : O₁} {o₂ : O₂} (h₁ : i₁ o₁ = u₁ z) (h₂ : i₂ o₂ = u₂ z) : p o₁ = q o₂ := by sorry
