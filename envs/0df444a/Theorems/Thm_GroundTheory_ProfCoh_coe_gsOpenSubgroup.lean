-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_gsOpenSubgroup
-- name    : GroundTheory.ProfCoh.coe_gsOpenSubgroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:24.190885+00:00
-- url     : https://prove2.me/theorems/a365e7f3-36a7-536e-beb4-1f220e3a4e55
-- title:
--   Prof Coh: coe gs Open Subgroup
-- statement:
--   The Prof Coh construction uses the coe gs Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L288-L290

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
variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem GroundTheory.ProfCoh.coe_gsOpenSubgroup : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) =
    fixingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) := by sorry
