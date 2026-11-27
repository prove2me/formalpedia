-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_isProSylow
-- name    : GroundTheory.ProfCoh.exists_isProSylow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:08.472966+00:00
-- url     : https://prove2.me/theorems/4f12091d-99d9-5403-b9ae-f7f2b84a1622
-- title:
--   Prof Coh: exists is Pro Sylow
-- statement:
--   The Prof Coh construction uses the exists is Pro Sylow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/NotDvdSuperIndexIffMap.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/NotDvdSuperIndexIffMap.lean#L175-L177

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Definitions.Def_GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
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
open Pointwise CategoryTheory
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.ProfCoh.exists_isProSylow : ∃ P : Subgroup G, IsProSylow p P := by sorry
