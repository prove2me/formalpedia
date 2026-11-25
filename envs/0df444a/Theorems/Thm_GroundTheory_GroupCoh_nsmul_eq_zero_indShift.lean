-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_indShift
-- name    : GroundTheory.GroupCoh.nsmul_eq_zero_indShift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:27.405882+00:00
-- url     : https://prove2.me/theorems/0253e5bb-a848-48e3-b10d-ec832b93cd44
-- title:
--   Group Coh: nsmul eq zero ind Shift
-- statement:
--   The Group Coh construction uses the nsmul eq zero ind Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L97-L104

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem GroundTheory.GroupCoh.nsmul_eq_zero_indShift [Fintype G] (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : indShift M, n • y = 0 := by sorry
