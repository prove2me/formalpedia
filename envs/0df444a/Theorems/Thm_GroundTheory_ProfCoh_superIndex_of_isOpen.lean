-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_superIndex_of_isOpen
-- name    : GroundTheory.ProfCoh.superIndex_of_isOpen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:56.852016+00:00
-- url     : https://prove2.me/theorems/414d60ee-4a57-5346-ac7f-94e198cd4844
-- title:
--   Prof Coh: super Index of is Open
-- statement:
--   The Prof Coh construction uses the super Index of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L137-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L137-L145

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
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
open Topology
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.ProfCoh.superIndex_of_isOpen [TotallyDisconnectedSpace G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : superIndex H = Supernatural.ofNat H.index := by sorry
