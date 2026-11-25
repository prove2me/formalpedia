-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isProSylow_iff
-- name    : GroundTheory.ProfCoh.isProSylow_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:32.518668+00:00
-- url     : https://prove2.me/theorems/7f00ab8a-e3a2-54e9-a4f0-aa3334325caf
-- title:
--   Prof Coh: is Pro Sylow iff
-- statement:
--   The Prof Coh construction uses the is Pro Sylow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/NotDvdSuperIndexIffMap.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/NotDvdSuperIndexIffMap.lean#L65-L70

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

theorem GroundTheory.ProfCoh.isProSylow_iff {P : Subgroup G} (hP : IsClosed (P : Set G)) :
    IsProSylow p P ↔ ∀ U : OpenNormalSubgroup G,
      IsPGroup p (P.map (QuotientGroup.mk' (U : Subgroup G))) ∧
        ¬ p ∣ (P.map (QuotientGroup.mk' (U : Subgroup G))).index := by sorry
