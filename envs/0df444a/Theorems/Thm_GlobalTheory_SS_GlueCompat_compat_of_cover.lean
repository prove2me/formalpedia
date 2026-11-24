-- Prove2me | Theorems.Thm_GlobalTheory_SS_GlueCompat_compat_of_cover
-- name    : GlobalTheory.SS.GlueCompat.compat_of_cover
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:02.931321+00:00
-- url     : https://prove2.me/theorems/ca381e9c-75b7-49d4-886f-8462a958f6f9
-- title:
--   Glue Compat: compat of cover
-- statement:
--   The Glue Compat construction uses the compat of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L253-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L253-L298

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]

theorem GlobalTheory.SS.GlueCompat.compat_of_cover {M₁ M₂ G N : Model R A} (g₁ : M₁.Y ⟶ G.Y) (g₂ : M₂.Y ⟶ G.Y) [IsOpenImmersion g₁.left]
    [IsOpenImmersion g₂.left] (j₁ : M₁.j ≫ g₁.left = G.j) (j₂ : M₂.j ≫ g₂.left = G.j)
    (cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left) (h₁ : Compat N M₁) (h₂ : Compat N M₂) :
    Compat N G := by sorry
