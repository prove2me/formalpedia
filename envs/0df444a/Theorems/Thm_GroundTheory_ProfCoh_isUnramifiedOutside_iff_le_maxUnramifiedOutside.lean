-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_iff_le_maxUnramifiedOutside
-- name    : GroundTheory.ProfCoh.isUnramifiedOutside_iff_le_maxUnramifiedOutside
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:26.665371+00:00
-- url     : https://prove2.me/theorems/a1b443c8-4173-4b2d-b04c-c6b4670e243c
-- title:
--   Prof Coh: is Unramified Outside iff le max Unramified Outside
-- statement:
--   The Prof Coh construction uses the is Unramified Outside iff le max Unramified Outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L70-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L70-L88

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
variable [NumberField F] [IsGalois F Ω]

theorem GroundTheory.ProfCoh.isUnramifiedOutside_iff_le_maxUnramifiedOutside {E : IntermediateField F Ω}
    [FiniteDimensional F E] : IsUnramifiedOutside S E ↔ E ≤ maxUnramifiedOutside F Ω S := by sorry
