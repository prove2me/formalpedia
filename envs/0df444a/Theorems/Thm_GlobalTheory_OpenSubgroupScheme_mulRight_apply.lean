-- Prove2me | Theorems.Thm_GlobalTheory_OpenSubgroupScheme_mulRight_apply
-- name    : GlobalTheory.OpenSubgroupScheme.mulRight_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:20.301248+00:00
-- url     : https://prove2.me/theorems/31fa521a-6da4-467c-9a42-40ac22ce4a1b
-- title:
--   Open Subgroup Scheme: mul Right apply
-- statement:
--   The Open Subgroup Scheme construction uses the mul Right apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L40-L43

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

theorem GlobalTheory.OpenSubgroupScheme.mulRight_apply [GrpObj G] (x g : 𝟙_ _ ⟶ G) :
    (GrpObj.mulRight g).hom.left (x.left (IsLocalRing.closedPoint K)) =
      (x * g).left (IsLocalRing.closedPoint K) := by sorry
