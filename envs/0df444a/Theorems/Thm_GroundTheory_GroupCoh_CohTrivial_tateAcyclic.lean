-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_tateAcyclic
-- name    : GroundTheory.GroupCoh.CohTrivial.tateAcyclic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:49.341978+00:00
-- url     : https://prove2.me/theorems/ea2d6a92-93da-5f2b-974f-24d77cca28ea
-- title:
--   Coh Trivial: tate Acyclic
-- statement:
--   The Coh Trivial construction uses the tate Acyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L94-L100

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

theorem GroundTheory.GroupCoh.CohTrivial.tateAcyclic [Fintype G] {A : Rep.{u} k G} (h : CohTrivial A) :
    TateAcyclic A := by sorry
