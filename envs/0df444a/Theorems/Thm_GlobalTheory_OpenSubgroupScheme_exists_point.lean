-- Prove2me | Theorems.Thm_GlobalTheory_OpenSubgroupScheme_exists_point
-- name    : GlobalTheory.OpenSubgroupScheme.exists_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:17.026619+00:00
-- url     : https://prove2.me/theorems/1f860d1f-7ea2-4cc3-8c6d-4326c21e312e
-- title:
--   Open Subgroup Scheme: exists point
-- statement:
--   The Open Subgroup Scheme construction uses the exists point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L31-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.OpenSubgroupScheme
variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}

theorem GlobalTheory.OpenSubgroupScheme.exists_point [IsAlgClosed K] [LocallyOfFiniteType G.hom] (y : G.left) (hy : IsClosed {y}) :
    ∃ x : 𝟙_ _ ⟶ G, x.left (IsLocalRing.closedPoint K) = y := by sorry
