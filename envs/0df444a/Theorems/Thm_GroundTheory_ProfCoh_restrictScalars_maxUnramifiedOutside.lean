-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_restrictScalars_maxUnramifiedOutside
-- name    : GroundTheory.ProfCoh.restrictScalars_maxUnramifiedOutside
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:11.179969+00:00
-- url     : https://prove2.me/theorems/6d28a01d-d110-4d6b-bcb2-c172103af2f3
-- title:
--   Prof Coh: restrict Scalars max Unramified Outside
-- statement:
--   The Prof Coh construction uses the restrict Scalars max Unramified Outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L146-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L146-L168

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
variable [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable [IsGalois F Ω]

theorem GroundTheory.ProfCoh.restrictScalars_maxUnramifiedOutside {L : IntermediateField F Ω} [FiniteDimensional F L]
    (hL : L ≤ maxUnramifiedOutside F Ω S) :
    (maxUnramifiedOutside L Ω (placesOver S)).restrictScalars F = maxUnramifiedOutside F Ω S := by sorry
