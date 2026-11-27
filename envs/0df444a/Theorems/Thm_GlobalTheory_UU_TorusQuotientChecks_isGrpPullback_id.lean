-- Prove2me | Theorems.Thm_GlobalTheory_UU_TorusQuotientChecks_isGrpPullback_id
-- name    : GlobalTheory.UU.TorusQuotientChecks.isGrpPullback_id
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:42.944922+00:00
-- url     : https://prove2.me/theorems/47b50a60-1d34-4d09-b534-bf69f6280ae2
-- title:
--   Torus Quotient Checks: is Grp Pullback id
-- statement:
--   The Torus Quotient Checks construction uses the is Grp Pullback id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/QuotientTiedToDatum.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/QuotientTiedToDatum.lean#L24-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMemCommonChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ESecCompOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackKernelBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothProjOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsAffineWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_QuotientTiedToDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.TorusQuotientChecks

theorem GlobalTheory.UU.TorusQuotientChecks.isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by sorry
