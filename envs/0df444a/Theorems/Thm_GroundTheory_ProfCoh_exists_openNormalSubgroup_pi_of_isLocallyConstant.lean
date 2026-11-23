-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_openNormalSubgroup_pi_of_isLocallyConstant
-- name    : GroundTheory.ProfCoh.exists_openNormalSubgroup_pi_of_isLocallyConstant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:11.448486+00:00
-- url     : https://prove2.me/theorems/1dac1d4c-be92-4032-803d-0ffc0d2b2661
-- title:
--   Prof Coh: exists open Normal Subgroup pi of is Locally Constant
-- statement:
--   The Prof Coh construction uses the exists open Normal Subgroup pi of is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Factor.lean#L12-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Factor.lean#L12-L48

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Factor
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
open Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem GroundTheory.ProfCoh.exists_openNormalSubgroup_pi_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : ι → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y := by sorry
