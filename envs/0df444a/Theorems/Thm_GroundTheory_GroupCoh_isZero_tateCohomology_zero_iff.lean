-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_iff
-- name    : GroundTheory.GroupCoh.isZero_tateCohomology_zero_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:42.21415+00:00
-- url     : https://prove2.me/theorems/46548f00-5c7f-4e5a-89c1-ec2b05b48255
-- title:
--   Group Coh: is Zero tate Cohomology zero iff
-- statement:
--   The Group Coh construction uses the is Zero tate Cohomology zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L239-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L239-L253

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

theorem GroundTheory.GroupCoh.isZero_tateCohomology_zero_iff (M : Rep.{u} R G) :
    IsZero (tateCohomology M 0) ↔ LinearMap.range M.ρ.norm = M.ρ.invariants := by sorry
