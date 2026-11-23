-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_iff
-- name    : GroundTheory.ProfCoh.isProPGroup_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:19.476875+00:00
-- url     : https://prove2.me/theorems/5f7ce14c-04c9-4595-9dd2-1004fc8d1f30
-- title:
--   Prof Coh: is Pro PGroup iff
-- statement:
--   The Prof Coh construction uses the is Pro PGroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L13-L23

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem GroundTheory.ProfCoh.isProPGroup_iff {p : ℕ} :
    IsProPGroup p G ↔ ∀ U : OpenNormalSubgroup G, ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ U := by sorry
