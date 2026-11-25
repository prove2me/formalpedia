-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_maxUnramifiedOutside_mono
-- name    : GroundTheory.ProfCoh.maxUnramifiedOutside_mono
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:35.607293+00:00
-- url     : https://prove2.me/theorems/79774e89-8071-470a-9b9b-a264683ae58d
-- title:
--   Prof Coh: max Unramified Outside mono
-- statement:
--   The Prof Coh construction uses the max Unramified Outside mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L20-L23

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
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
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem GroundTheory.ProfCoh.maxUnramifiedOutside_mono {S T : Set (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    maxUnramifiedOutside F Ω S ≤ maxUnramifiedOutside F Ω T := by sorry
