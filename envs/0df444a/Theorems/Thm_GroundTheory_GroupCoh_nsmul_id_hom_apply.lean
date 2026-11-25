-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_nsmul_id_hom_apply
-- name    : GroundTheory.GroupCoh.nsmul_id_hom_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:39.733418+00:00
-- url     : https://prove2.me/theorems/b74aff6e-6f06-46b6-a05a-e029b57aefde
-- title:
--   Group Coh: nsmul id hom apply
-- statement:
--   The Group Coh construction uses the nsmul id hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L72-L73

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

theorem GroundTheory.GroupCoh.nsmul_id_hom_apply (M : Rep.{u} k G) (n : ℕ) (x : M) : (n • 𝟙 M).hom x = n • x := by sorry
