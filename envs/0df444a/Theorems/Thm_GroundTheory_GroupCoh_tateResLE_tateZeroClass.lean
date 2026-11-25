-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateResLE_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateResLE_tateZeroClass
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:51.162908+00:00
-- url     : https://prove2.me/theorems/a297114e-4563-505d-ad0a-e76580cb8cc0
-- title:
--   Group Coh: tate Res LE tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Res LE tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L182-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L182-L197

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

theorem GroundTheory.GroupCoh.tateResLE_tateZeroClass (A : Rep.{u} k G) (y : (res U.subtype A).ρ.invariants) :
    ((tateResLE h 0).app A).hom (tateZeroClass (res U.subtype A) y) =
      tateZeroClass (res W.subtype A) (invariantsLE h y) := by sorry
