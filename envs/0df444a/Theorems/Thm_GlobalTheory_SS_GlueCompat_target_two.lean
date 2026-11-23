-- Prove2me | Theorems.Thm_GlobalTheory_SS_GlueCompat_target_two
-- name    : GlobalTheory.SS.GlueCompat.target_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:34.208424+00:00
-- url     : https://prove2.me/theorems/fcce2f9e-6e2d-48e0-b9af-a178f2e13d77
-- title:
--   Glue Compat: target two
-- statement:
--   The Glue Compat construction uses the target two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L27-L36

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

theorem GlobalTheory.SS.GlueCompat.target_two (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {X Y U V U' V' : Scheme.{0}}
    {f : X ⟶ Y} {u : U ⟶ Y} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : Y, x ∈ Set.range u ∨ x ∈ Set.range v) {a : U' ⟶ X} {b : U' ⟶ U} {c : V' ⟶ X} {d : V' ⟶ V}
    (h₁ : IsPullback a b f u) (h₂ : IsPullback c d f v) (hb : P b) (hd : P d) : P f := by sorry
