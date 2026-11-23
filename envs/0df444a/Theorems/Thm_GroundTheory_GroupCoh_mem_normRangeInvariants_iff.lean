-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_mem_normRangeInvariants_iff
-- name    : GroundTheory.GroupCoh.mem_normRangeInvariants_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:01.012825+00:00
-- url     : https://prove2.me/theorems/87d2ba2b-3299-4888-bd35-eaa6b74aba0c
-- title:
--   Group Coh: mem norm Range Invariants iff
-- statement:
--   The Group Coh construction uses the mem norm Range Invariants iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L60-L61

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
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
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.mem_normRangeInvariants_iff (M : Rep.{u} R G) (x : M.ρ.invariants) :
    x ∈ normRangeInvariants M ↔ ∃ m, M.ρ.norm m = x := by sorry
