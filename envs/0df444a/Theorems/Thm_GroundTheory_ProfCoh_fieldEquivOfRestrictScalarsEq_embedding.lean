-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_fieldEquivOfRestrictScalarsEq_embedding
-- name    : GroundTheory.ProfCoh.fieldEquivOfRestrictScalarsEq_embedding
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:18.614964+00:00
-- url     : https://prove2.me/theorems/67671e25-ee78-46dd-9836-1336cd8e6dad
-- title:
--   Prof Coh: field Equiv Of Restrict Scalars Eq embedding
-- statement:
--   The Prof Coh construction uses the field Equiv Of Restrict Scalars Eq embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L57-L59

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
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
open NumberField IsDedekindDomain
universe u
noncomputable section
variable {F L Ω : Type u} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] {E : IntermediateField F Ω} {E' : IntermediateField L Ω}
  (h : E'.restrictScalars F = E)

theorem GroundTheory.ProfCoh.fieldEquivOfRestrictScalarsEq_embedding (x : L) :
    fieldEquivOfRestrictScalarsEq h (embeddingOfRestrictScalarsEq h x) = algebraMap L E' x := by sorry
