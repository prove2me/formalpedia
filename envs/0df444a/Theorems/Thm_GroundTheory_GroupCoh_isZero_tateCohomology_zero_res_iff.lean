-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_res_iff
-- name    : GroundTheory.GroupCoh.isZero_tateCohomology_zero_res_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:00.579572+00:00
-- url     : https://prove2.me/theorems/805a4b26-0aff-5c7f-b39b-06f3a019ad33
-- title:
--   Group Coh: is Zero tate Cohomology zero res iff
-- statement:
--   The Group Coh construction uses the is Zero tate Cohomology zero res iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L24-L41

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
variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)
include hf

theorem GroundTheory.GroupCoh.isZero_tateCohomology_zero_res_iff (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) 0) ↔ IsZero (tateCohomology B 0) := by sorry
