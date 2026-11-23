-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
-- name    : GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:33.417668+00:00
-- url     : https://prove2.me/theorems/aaa9fc0e-e211-4c03-8612-8f71aedd6469
-- title:
--   Prof Coh: coe open Normal Subgroup Equiv symm apply
-- statement:
--   The Prof Coh construction uses the coe open Normal Subgroup Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L147-L150

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

theorem GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply (E : FiniteGaloisIntermediateField K L) :
    ((openNormalSubgroupEquiv.symm (OrderDual.toDual E) : OpenNormalSubgroup Gal(L/K)) :
      Subgroup Gal(L/K)) = E.fixingSubgroup := by sorry

attribute [defeq] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
