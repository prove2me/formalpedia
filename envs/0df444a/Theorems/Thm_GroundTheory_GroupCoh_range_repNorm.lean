-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_range_repNorm
-- name    : GroundTheory.GroupCoh.range_repNorm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:14.639846+00:00
-- url     : https://prove2.me/theorems/41ca61f9-452b-4b56-8934-a246e9b36c89
-- title:
--   Group Coh: range rep Norm
-- statement:
--   The Group Coh construction uses the range rep Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L37-L41

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_HerbrandTate
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
universe u
open CategoryTheory
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by sorry
