-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_finiteGalois_le
-- name    : GroundTheory.ProfCoh.exists_finiteGalois_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:52.045128+00:00
-- url     : https://prove2.me/theorems/5799a4eb-c0f6-414d-8d9b-755afac748b8
-- title:
--   Prof Coh: exists finite Galois le
-- statement:
--   The Prof Coh construction uses the exists finite Galois le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L158-L162

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

theorem GroundTheory.ProfCoh.exists_finiteGalois_le (E : IntermediateField K L) [FiniteDimensional K E] :
    ∃ F : FiniteGaloisIntermediateField K L, E ≤ F.toIntermediateField := by sorry
