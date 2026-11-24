-- Prove2me | Theorems.Thm_GlobalTheory_ChartModel_isSeparated_of_two
-- name    : GlobalTheory.ChartModel.isSeparated_of_two
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:46.008799+00:00
-- url     : https://prove2.me/theorems/8978e350-a551-43f1-98b6-2fa82e951570
-- title:
--   Chart Model: is Separated of two
-- statement:
--   The Chart Model construction uses the is Separated of two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChart.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChart.lean#L35-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
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
open GlobalTheory GlobalTheory.ChartModel
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.ChartModel.isSeparated_of_two {U V Y S : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion u]
    [IsOpenImmersion v] [IsSeparated (u ≫ f)] [IsSeparated (v ≫ f)]
    (h : ∀ x y : Y, f x = f y → (x ∈ Set.range u ∧ y ∈ Set.range u) ∨ (x ∈ Set.range v ∧ y ∈ Set.range v)) :
    IsSeparated f := by sorry
