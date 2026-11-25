-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_superIndex_eq_mul
-- name    : GroundTheory.ProfCoh.superIndex_eq_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:44.872804+00:00
-- url     : https://prove2.me/theorems/784f54c5-8e07-4916-ad92-d7973ee3ae74
-- title:
--   Prof Coh: super Index eq mul
-- statement:
--   The Prof Coh construction uses the super Index eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L147-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L147-L154

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

theorem GroundTheory.ProfCoh.superIndex_eq_mul [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex K = superIndex H * superRelIndex K H := by sorry
