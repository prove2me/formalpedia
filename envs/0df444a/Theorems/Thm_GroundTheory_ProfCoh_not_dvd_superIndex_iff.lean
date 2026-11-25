-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_not_dvd_superIndex_iff
-- name    : GroundTheory.ProfCoh.not_dvd_superIndex_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:52.858962+00:00
-- url     : https://prove2.me/theorems/865629f4-eba9-47ba-bc2d-8d3d11904150
-- title:
--   Prof Coh: not dvd super Index iff
-- statement:
--   The Prof Coh construction uses the not dvd super Index iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L94-L99

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

theorem GroundTheory.ProfCoh.not_dvd_superIndex_iff (p : Nat.Primes) (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ (p : ℕ) ∣ (H ⊔ (U : Subgroup G)).index := by sorry
