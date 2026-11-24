-- Prove2me | Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_point_one
-- name    : GlobalTheory.SS.ArcInf.TwoVarSetup.point_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:34:25.368851+00:00
-- url     : https://prove2.me/theorems/03674cc8-9e4a-4158-af68-ad657967f1a2
-- title:
--   Two Var Setup: point one
-- statement:
--   The Two Var Setup construction uses the point one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsArcQuotientTwoVariableCoords.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsArcQuotientTwoVariableCoords.lean#L83-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasicOpenFactorFieldPointAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsArcQuotientTwoVariableCoords
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
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf GlobalTheory.SS.ArcInf.TwoVarSetup
variable {k : Type} [Field k]

theorem GlobalTheory.SS.ArcInf.TwoVarSetup.point_one {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} (h : algOverHom ε ≫ j = 1) (F : Type) [CommRing F] [Algebra k F] :
    algOverHom ((Algebra.ofId k F).comp ε) ≫ j = 1 := by sorry
