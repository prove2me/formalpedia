-- Prove2me | Theorems.Thm_GlobalTheory_RedPts_eq_one_of_pow_of_closedPoint
-- name    : GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:21:34.67123+00:00
-- url     : https://prove2.me/theorems/4af07a0e-0ff1-4167-923a-465e03402cbe
-- title:
--   Red Pts: eq one of pow of closed Point
-- statement:
--   The Red Pts construction uses the eq one of pow of closed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOneOfPowOfClosedPoint.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOneOfPowOfClosedPoint.lean#L46-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOneOfPowOfClosedPoint
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
open GlobalTheory GlobalTheory.RedPts
variable {S : Scheme.{0}}

theorem GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint (G : Over S) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] {R : Type} [CommRing R] [IsLocalRing R] (p : Sp R ⟶ S) {n : ℕ}
    (hn : IsUnit (n : R)) (x : Over.mk p ⟶ G) (hx : x ^ n = 1) {Z : Over S} (j : Z ⟶ Over.mk p)
    (hj : IsLocalRing.closedPoint R ∈ Set.range (show Z.left ⟶ Sp R from j.left)) (h : j ≫ x = 1) :
    x = 1 := by sorry
