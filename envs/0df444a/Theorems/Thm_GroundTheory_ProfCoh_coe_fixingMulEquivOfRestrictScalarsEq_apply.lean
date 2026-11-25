-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_fixingMulEquivOfRestrictScalarsEq_apply
-- name    : GroundTheory.ProfCoh.coe_fixingMulEquivOfRestrictScalarsEq_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:52:36.703803+00:00
-- url     : https://prove2.me/theorems/dcc8b4d5-b281-465d-9a8d-0a20ff77cda0
-- title:
--   Prof Coh: coe fixing Mul Equiv Of Restrict Scalars Eq apply
-- statement:
--   The Prof Coh construction uses the coe fixing Mul Equiv Of Restrict Scalars Eq apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L102-L105

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

theorem GroundTheory.ProfCoh.coe_fixingMulEquivOfRestrictScalarsEq_apply (σ : fixingOfRestrictScalarsEq h) (x : E') :
    ((fixingMulEquivOfRestrictScalarsEq h σ x : E') : Ω) =
      ((σ : Gal(E/F)) ((fieldEquivOfRestrictScalarsEq h).symm x) : Ω) := by sorry
