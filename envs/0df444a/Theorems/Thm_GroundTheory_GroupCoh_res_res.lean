-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_res_res
-- name    : GroundTheory.GroupCoh.res_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:25:56.40185+00:00
-- url     : https://prove2.me/theorems/d17b9e62-8d2c-4cdd-a288-a6796aeca3f7
-- title:
--   Group Coh: res res
-- statement:
--   The Group Coh construction uses the res res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L90-L92

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
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
omit [Group G]

theorem GroundTheory.GroupCoh.res_res {H K : Type u} [Group H] [Group K] [Group G] (f : H →* K) (g : K →* G)
    (A : Rep.{u} k G) : res f (res g A) = res (g.comp f) A := by sorry
