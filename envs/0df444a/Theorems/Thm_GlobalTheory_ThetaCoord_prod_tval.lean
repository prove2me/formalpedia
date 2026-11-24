-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCoord_prod_tval
-- name    : GlobalTheory.ThetaCoord.prod_tval
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:17:23.54133+00:00
-- url     : https://prove2.me/theorems/bbc0776e-4ec2-479a-893e-dc911584bc15
-- title:
--   Theta Coord: prod tval
-- statement:
--   The Theta Coord construction uses the prod tval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L115-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}

theorem GlobalTheory.ThetaCoord.prod_tval {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) (π : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    ∏ j ∈ Finset.range n, tval θ (lift π ((π ≫ x) ^ j * p)).left z J = 1 := by sorry
