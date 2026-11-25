-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_ind_bot
-- name    : GroundTheory.GroupCoh.tateAcyclic_ind_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:05.348803+00:00
-- url     : https://prove2.me/theorems/a8aa0c88-963b-42a6-8b12-77d36e36b28c
-- title:
--   Group Coh: tate Acyclic ind bot
-- statement:
--   The Group Coh construction uses the tate Acyclic ind bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L141-L142

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k (⊥ : Subgroup G))

theorem GroundTheory.GroupCoh.tateAcyclic_ind_bot : TateAcyclic (ind (⊥ : Subgroup G).subtype B) := by sorry
