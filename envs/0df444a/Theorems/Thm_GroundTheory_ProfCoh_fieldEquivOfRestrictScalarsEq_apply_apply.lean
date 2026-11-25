-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_fieldEquivOfRestrictScalarsEq_apply_apply
-- name    : GroundTheory.ProfCoh.fieldEquivOfRestrictScalarsEq_apply_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:44.90549+00:00
-- url     : https://prove2.me/theorems/e73254be-d5f6-4690-9a7b-6e733a10567e
-- title:
--   Prof Coh: field Equiv Of Restrict Scalars Eq apply apply
-- statement:
--   The Prof Coh construction uses the field Equiv Of Restrict Scalars Eq apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L107-L110

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

theorem GroundTheory.ProfCoh.fieldEquivOfRestrictScalarsEq_apply_apply (σ : fixingOfRestrictScalarsEq h) (x : E) :
    fieldEquivOfRestrictScalarsEq h ((σ : Gal(E/F)) x) =
      fixingMulEquivOfRestrictScalarsEq h σ (fieldEquivOfRestrictScalarsEq h x) := by sorry
