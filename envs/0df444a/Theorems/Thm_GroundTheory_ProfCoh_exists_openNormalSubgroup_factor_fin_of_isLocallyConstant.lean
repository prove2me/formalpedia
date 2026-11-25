-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_openNormalSubgroup_factor_fin_of_isLocallyConstant
-- name    : GroundTheory.ProfCoh.exists_openNormalSubgroup_factor_fin_of_isLocallyConstant
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:17.338497+00:00
-- url     : https://prove2.me/theorems/f7e8d732-cca1-49d1-a0c7-24d328c73c9f
-- title:
--   Prof Coh: exists open Normal Subgroup factor fin of is Locally Constant
-- statement:
--   The Prof Coh construction uses the exists open Normal Subgroup factor fin of is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Factor.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Factor.lean#L63-L67

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

theorem GroundTheory.ProfCoh.exists_openNormalSubgroup_factor_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (Fin n → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) := by sorry
