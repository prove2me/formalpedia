-- Prove2me | Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_exists_liftAway
-- name    : GlobalTheory.SS.ArcInf.TwoVarSetup.exists_liftAway
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:34:07.136356+00:00
-- url     : https://prove2.me/theorems/9c13bbbc-8c83-460f-802f-38adfbeec3b9
-- title:
--   Two Var Setup: exists lift Away
-- statement:
--   The Two Var Setup construction uses the exists lift Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsArcQuotientTwoVariableCoords.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsArcQuotientTwoVariableCoords.lean#L18-L25

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

theorem GlobalTheory.SS.ArcInf.TwoVarSetup.exists_liftAway {k R F : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing F] [Algebra k F]
    (x : R) (τ : R →ₐ[k] F) (h : IsUnit (τ x)) :
    ∃ τ' : Localization.Away x →ₐ[k] F, ∀ y, τ' (algebraMap R _ y) = τ y := by sorry
