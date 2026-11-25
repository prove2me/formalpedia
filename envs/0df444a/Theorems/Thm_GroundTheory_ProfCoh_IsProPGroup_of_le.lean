-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_IsProPGroup_of_le
-- name    : GroundTheory.ProfCoh.IsProPGroup.of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:16.056823+00:00
-- url     : https://prove2.me/theorems/99c72bfa-f3eb-42a3-a4f4-11f2cb5b448d
-- title:
--   Is Pro PGroup: of le
-- statement:
--   The Is Pro PGroup construction uses the of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L81-L84

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

theorem GroundTheory.ProfCoh.IsProPGroup.of_le {p : ℕ} {H K : Subgroup G} (hH : IsProPGroup p H) (hKH : K ≤ H) :
    IsProPGroup p K := by sorry
