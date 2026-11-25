-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular
-- name    : GroundTheory.GroupCoh.tateAcyclic_leftRegular
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:02.646333+00:00
-- url     : https://prove2.me/theorems/5b7ed886-b66e-4648-8fea-fe13f37cf296
-- title:
--   Group Coh: tate Acyclic left Regular
-- statement:
--   The Group Coh construction uses the tate Acyclic left Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L95-L96

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
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
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k G)

theorem GroundTheory.GroupCoh.tateAcyclic_leftRegular : TateAcyclic (leftRegular k G) := by sorry
