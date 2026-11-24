-- Prove2me | Theorems.Thm_GlobalTheory_ChartModel_exists_glue_chart
-- name    : GlobalTheory.ChartModel.exists_glue_chart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:54.950151+00:00
-- url     : https://prove2.me/theorems/a9e072f7-9f23-4673-9703-241fe1b7b5f1
-- title:
--   Chart Model: exists glue chart
-- statement:
--   The Chart Model construction uses the exists glue chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChart.lean#L50-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChart.lean#L50-L97

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

theorem GlobalTheory.ChartModel.exists_glue_chart {S T A X W : Scheme.{0}} (i : T ⟶ S) [IsOpenImmersion i] (a : A ⟶ T) (c : X ⟶ S)
    {p : W ⟶ X} {w : W ⟶ T} (hW : IsPullback p w c i) (u : W ⟶ A) [IsOpenImmersion u] (hu : u ≫ a = w)
    [Smooth a] [IsSeparated a] [Smooth c] [IsSeparated c] [CompactSpace A] [CompactSpace X] :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (g : X ⟶ Y) (j : A ⟶ Y), IsOpenImmersion g ∧ IsPullback j a f i ∧ g ≫ f = c ∧
      p ≫ g = u ≫ j ∧ Smooth f ∧ IsSeparated f ∧ CompactSpace Y ∧ ∀ y, f y ∉ Set.range i → y ∈ Set.range g := by sorry
