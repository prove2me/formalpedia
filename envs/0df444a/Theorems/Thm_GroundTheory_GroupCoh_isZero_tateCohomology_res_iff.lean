-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_res_iff
-- name    : GroundTheory.GroupCoh.isZero_tateCohomology_res_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:14:49.328454+00:00
-- url     : https://prove2.me/theorems/45de53cb-0d88-503e-a836-a0a1ff829658
-- title:
--   Group Coh: is Zero tate Cohomology res iff
-- statement:
--   The Group Coh construction uses the is Zero tate Cohomology res iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L50-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L50-L77

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

theorem GroundTheory.GroupCoh.isZero_tateCohomology_res_iff (n : ℤ) (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n) := by sorry
