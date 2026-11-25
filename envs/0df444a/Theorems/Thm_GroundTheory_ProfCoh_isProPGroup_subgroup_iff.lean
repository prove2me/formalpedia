-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_subgroup_iff
-- name    : GroundTheory.ProfCoh.isProPGroup_subgroup_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:06.279991+00:00
-- url     : https://prove2.me/theorems/19e725ac-b9e8-42b8-8870-f4f8623af581
-- title:
--   Prof Coh: is Pro PGroup subgroup iff
-- statement:
--   The Prof Coh construction uses the is Pro PGroup subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L59-L73

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
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

theorem GroundTheory.ProfCoh.isProPGroup_subgroup_iff {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔ ∀ U : OpenNormalSubgroup G, ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by sorry
