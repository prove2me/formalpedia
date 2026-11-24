-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_finiteGalois_mem
-- name    : GroundTheory.ProfCoh.exists_finiteGalois_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:04.449636+00:00
-- url     : https://prove2.me/theorems/8e04e013-5ef7-4738-92c4-3dff678d2529
-- title:
--   Prof Coh: exists finite Galois mem
-- statement:
--   The Prof Coh construction uses the exists finite Galois mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean#L164-L167

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

theorem GroundTheory.ProfCoh.exists_finiteGalois_mem (x : L) :
    ∃ F : FiniteGaloisIntermediateField K L, x ∈ F.toIntermediateField := by sorry
