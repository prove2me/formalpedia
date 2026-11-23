-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_index_sup_ne_zero
-- name    : GroundTheory.ProfCoh.index_sup_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:19.990408+00:00
-- url     : https://prove2.me/theorems/bfe2cb91-d7ff-4bad-9080-665a74ab030b
-- title:
--   Prof Coh: index sup ne zero
-- statement:
--   The Prof Coh construction uses the index sup ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L68-L71

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

theorem GroundTheory.ProfCoh.index_sup_ne_zero (H : Subgroup G) (U : OpenNormalSubgroup G) :
    (H ⊔ (U : Subgroup G)).index ≠ 0 := by sorry
