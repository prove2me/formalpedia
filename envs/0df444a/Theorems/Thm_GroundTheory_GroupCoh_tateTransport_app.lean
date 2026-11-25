-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateTransport_app
-- name    : GroundTheory.GroupCoh.tateTransport_app
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:12.99656+00:00
-- url     : https://prove2.me/theorems/7c6c596e-9a5a-5b81-84e2-5e9b878e5815
-- title:
--   Group Coh: tate Transport app
-- statement:
--   The Group Coh construction uses the tate Transport app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean#L85-L86

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

theorem GroundTheory.GroupCoh.tateTransport_app (n : ℤ) (B : Rep.{u} k K) :
    (tateTransport e n).app B = HomologicalComplex.homologyMap (tateTransportComplex e B) n := by sorry
