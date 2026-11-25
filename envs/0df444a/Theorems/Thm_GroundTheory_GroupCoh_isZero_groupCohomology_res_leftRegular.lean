-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_groupCohomology_res_leftRegular
-- name    : GroundTheory.GroupCoh.isZero_groupCohomology_res_leftRegular
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:29.328088+00:00
-- url     : https://prove2.me/theorems/8b503e8a-dea6-560d-965e-3f12cc15b7c3
-- title:
--   Group Coh: is Zero group Cohomology res left Regular
-- statement:
--   The Group Coh construction uses the is Zero group Cohomology res left Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L85-L87

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

theorem GroundTheory.GroupCoh.isZero_groupCohomology_res_leftRegular (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (res S.subtype (Rep.leftRegular ℤ G)) n) := by sorry
