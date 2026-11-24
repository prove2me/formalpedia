-- Prove2me | Theorems.Thm_GlobalTheory_SS_FinUnion_le_of_law
-- name    : GlobalTheory.SS.FinUnion.le_of_law
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:16.515615+00:00
-- url     : https://prove2.me/theorems/184547fd-a312-4efa-b72e-d3e103ba9a8c
-- title:
--   Fin Union: le of law
-- statement:
--   The Fin Union construction uses the le of law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnionTranslates.lean#L174-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnionTranslates.lean#L174-L253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [GrpObj A] [IsCommMonObj A]
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.SS.FinUnion.le_of_law [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] {M G : Model R A} (hM : Strict M)
    (m : M.Y ⊗ M.Y ⟶ G.Y) (hm : (M.prod M).j ≫ m.left = (μ[A]).left ≫ G.j) (a : 𝟙_ (Over (Sp K)) ⟶ A)
    (ha : GenIso M M (transl a).hom) (hc : Compat (M.twist (transl a)) G) : (M.twist (transl a)).Le G := by sorry
