-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
-- name    : GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:56.759906+00:00
-- url     : https://prove2.me/theorems/c4e0413f-a135-4e4c-92a2-93a63b4b3ab1
-- title:
--   Prof Coh: open Normal Subgroup Equiv apply
-- statement:
--   The Prof Coh construction uses the open Normal Subgroup Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L141-L144

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open IntermediateField InfiniteGalois
universe u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

theorem GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply (U : OpenNormalSubgroup Gal(L/K)) :
    (OrderDual.ofDual (openNormalSubgroupEquiv U)).toIntermediateField =
      fixedField (U : Subgroup Gal(L/K)) := by sorry

attribute [defeq] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
