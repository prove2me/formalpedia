-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_groupCohomology_of_bijective_nsmul
-- name    : GroundTheory.GroupCoh.isZero_groupCohomology_of_bijective_nsmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:04.491745+00:00
-- url     : https://prove2.me/theorems/a9fb82b5-2df9-45ff-9d11-626aeafea79c
-- title:
--   Group Coh: is Zero group Cohomology of bijective nsmul
-- statement:
--   The Group Coh construction uses the is Zero group Cohomology of bijective nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/UniquelyDivisible.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/UniquelyDivisible.lean#L38-L42

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.isZero_groupCohomology_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology M n) := by sorry
