-- Prove2me | Theorems.Thm_GlobalTheory_SS_OrdTwist_exists_std
-- name    : GlobalTheory.SS.OrdTwist.exists_std
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:42:04.893747+00:00
-- url     : https://prove2.me/theorems/9c957a0d-ece9-492b-be72-c1e46de34351
-- title:
--   Ord Twist: exists std
-- statement:
--   The Ord Twist construction uses the exists std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyAutomorphismShiftsJacobianOrder.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyAutomorphismShiftsJacobianOrder.lean#L64-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]

theorem GlobalTheory.SS.OrdTwist.exists_std {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) (U : A.left.Opens) (x : A.left) (hx : x ∈ U) :
    ∃ V : A.left.Opens, V ≤ U ∧ x ∈ V ∧ (cstK A V).IsStandardSmoothOfRelativeDimension n := by sorry
