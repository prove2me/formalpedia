-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateRes_comp_isoGroupCohomology
-- name    : GroundTheory.GroupCoh.tateRes_comp_isoGroupCohomology
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:44.238904+00:00
-- url     : https://prove2.me/theorems/5e4f23ad-7bd9-42b9-b2ec-6ec40eb82b6a
-- title:
--   Group Coh: tate Res comp iso Group Cohomology
-- statement:
--   The Group Coh construction uses the tate Res comp iso Group Cohomology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L193-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L193-L225

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem GroundTheory.GroupCoh.tateRes_comp_isoGroupCohomology (n : ℕ) [NeZero n] (A : Rep.{u} k G) :
    (tateRes S n).app A ≫ (TateCohomology.isoGroupCohomology n).hom.app (res S.subtype A) =
      (TateCohomology.isoGroupCohomology n).hom.app A ≫
        groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n := by sorry
