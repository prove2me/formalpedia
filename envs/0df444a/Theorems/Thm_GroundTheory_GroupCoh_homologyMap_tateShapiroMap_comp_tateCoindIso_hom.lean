-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateShapiroMap_comp_tateCoindIso_hom
-- name    : GroundTheory.GroupCoh.homologyMap_tateShapiroMap_comp_tateCoindIso_hom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:09.586961+00:00
-- url     : https://prove2.me/theorems/2450656a-da53-56ad-812c-b5f5ab03975e
-- title:
--   Group Coh: homology Map tate Shapiro Map comp tate Coind Iso hom
-- statement:
--   The Group Coh construction uses the homology Map tate Shapiro Map comp tate Coind Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L384-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L384-L386

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]

theorem GroundTheory.GroupCoh.homologyMap_tateShapiroMap_comp_tateCoindIso_hom (B : Rep.{u} k S) (n : ℤ) :
    HomologicalComplex.homologyMap (tateShapiroMap S B) n ≫ (tateCoindIso S B n).hom = 𝟙 _ := by sorry
