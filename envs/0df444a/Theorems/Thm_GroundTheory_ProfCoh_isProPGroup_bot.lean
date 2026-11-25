-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_bot
-- name    : GroundTheory.ProfCoh.isProPGroup_bot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:14.349846+00:00
-- url     : https://prove2.me/theorems/b3b61f73-a127-4b71-aa96-d00bd28a92bc
-- title:
--   Prof Coh: is Pro PGroup bot
-- statement:
--   The Prof Coh construction uses the is Pro PGroup bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/IsProPGroupSubgroupIffIsPGroupMap.lean#L86-L90

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

theorem GroundTheory.ProfCoh.isProPGroup_bot (p : ℕ) : IsProPGroup p (⊥ : Subgroup G) := by sorry
