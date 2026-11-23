-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_relIndex_sup_ne_zero
-- name    : GroundTheory.ProfCoh.relIndex_sup_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:57.276447+00:00
-- url     : https://prove2.me/theorems/758a2236-b377-41e6-9fa8-872aeeb91b9d
-- title:
--   Prof Coh: rel Index sup ne zero
-- statement:
--   The Prof Coh construction uses the rel Index sup ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L73-L77

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

theorem GroundTheory.ProfCoh.relIndex_sup_ne_zero (K H : Subgroup G) (U : OpenNormalSubgroup G) :
    (K ⊔ (U : Subgroup G)).relIndex H ≠ 0 := by sorry
