-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_of_le
-- name    : GroundTheory.GroupCoh.tateAcyclic_res_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:59.777221+00:00
-- url     : https://prove2.me/theorems/d504fcf8-8aae-43f4-be5a-e9cc2bdcd7f7
-- title:
--   Group Coh: tate Acyclic res of le
-- statement:
--   The Group Coh construction uses the tate Acyclic res of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivial.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivial.lean#L65-L72

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
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

theorem GroundTheory.GroupCoh.tateAcyclic_res_of_le {A : Rep.{u} k G} {P : Subgroup G} (hP : CohTrivial (res P.subtype A))
    {V : Subgroup G} [Fintype V] (hV : V ≤ P) : TateAcyclic (res V.subtype A) := by sorry
