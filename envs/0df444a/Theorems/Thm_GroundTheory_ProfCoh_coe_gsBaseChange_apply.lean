-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_gsBaseChange_apply
-- name    : GroundTheory.ProfCoh.coe_gsBaseChange_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:04:44.237566+00:00
-- url     : https://prove2.me/theorems/4d449e19-0e5a-4d4f-9728-4116127897fd
-- title:
--   Prof Coh: coe gs Base Change apply
-- statement:
--   The Prof Coh construction uses the coe gs Base Change apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L317-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L317-L321

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
variable {S}

theorem GroundTheory.ProfCoh.coe_gsBaseChange_apply (σ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)))
    (x : maxUnramifiedOutside L Ω (placesOver S)) :
    ((gsBaseChange S hL σ x : maxUnramifiedOutside L Ω (placesOver S)) : Ω) =
      ((σ : galUnramifiedOutside F Ω S) ((gsFieldEquiv hL).symm x) : Ω) := by sorry
