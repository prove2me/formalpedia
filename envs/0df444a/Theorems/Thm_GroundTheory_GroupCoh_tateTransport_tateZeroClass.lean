-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateTransport_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateTransport_tateZeroClass
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:53:29.663004+00:00
-- url     : https://prove2.me/theorems/1da0b316-b107-4591-a6ff-ba4d7d504df7
-- title:
--   Group Coh: tate Transport tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Transport tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean#L124-L127

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
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
open CategoryTheory Limits Rep groupCohomology groupHomology
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K]
variable [Fintype H] [Fintype K] (e : H ≃* K)

theorem GroundTheory.GroupCoh.tateTransport_tateZeroClass (B : Rep.{u} k K) (x : B.ρ.invariants) :
    ((tateTransport e 0).app B).hom (tateZeroClass B x) =
      tateZeroClass (res (e : H →* K) B) (invariantsTransport e x) := by sorry
