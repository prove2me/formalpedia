-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_leftRegular
-- name    : GroundTheory.GroupCoh.tateAcyclic_res_leftRegular
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:36.167703+00:00
-- url     : https://prove2.me/theorems/37cde9e6-7176-5434-af9e-8a6689855f9b
-- title:
--   Group Coh: tate Acyclic res left Regular
-- statement:
--   The Group Coh construction uses the tate Acyclic res left Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L82-L83

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]

theorem GroundTheory.GroupCoh.tateAcyclic_res_leftRegular : TateAcyclic (res S.subtype (Rep.leftRegular ℤ G)) := by sorry
