-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCoresLE_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateCoresLE_tateZeroClass
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:07.162604+00:00
-- url     : https://prove2.me/theorems/cb3dec4b-8af0-5f58-83ab-4e723420ed04
-- title:
--   Group Coh: tate Cores LE tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Cores LE tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L206-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L206-L218

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {U W : Subgroup G} (h : W ≤ U)
variable [Fintype U] [Fintype W]

theorem GroundTheory.GroupCoh.tateCoresLE_tateZeroClass (A : Rep.{u} k G) (y : (res W.subtype A).ρ.invariants) :
    ((tateCoresLE h 0).app A).hom (tateZeroClass (res W.subtype A) y) =
      tateZeroClass (res U.subtype A) (transferInv (W.subgroupOf U) (invariantsSubgroupOf U y)) := by sorry
