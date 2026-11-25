-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_gsFieldEquiv_apply_apply
-- name    : GroundTheory.ProfCoh.gsFieldEquiv_apply_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:26.885674+00:00
-- url     : https://prove2.me/theorems/dd74f3ff-fb51-5c78-b9b3-f0af83626859
-- title:
--   Prof Coh: gs Field Equiv apply apply
-- statement:
--   The Prof Coh construction uses the gs Field Equiv apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L323-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L323-L326

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

theorem GroundTheory.ProfCoh.gsFieldEquiv_apply_apply (σ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)))
    (x : maxUnramifiedOutside F Ω S) :
    gsFieldEquiv hL ((σ : galUnramifiedOutside F Ω S) x) = gsBaseChange S hL σ (gsFieldEquiv hL x) := by sorry
