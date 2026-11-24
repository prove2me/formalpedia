-- Prove2me | Theorems.Thm_GlobalTheory_OpenSubgroupScheme_comp_mulRight
-- name    : GlobalTheory.OpenSubgroupScheme.comp_mulRight
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:06.947119+00:00
-- url     : https://prove2.me/theorems/1c7c34e5-e5f0-4c84-ad5f-f9852808dc02
-- title:
--   Open Subgroup Scheme: comp mul Right
-- statement:
--   The Open Subgroup Scheme construction uses the comp mul Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L36-L38

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

theorem GlobalTheory.OpenSubgroupScheme.comp_mulRight [GrpObj G] (x g : 𝟙_ _ ⟶ G) : x ≫ (GrpObj.mulRight g).hom = x * g := by sorry
