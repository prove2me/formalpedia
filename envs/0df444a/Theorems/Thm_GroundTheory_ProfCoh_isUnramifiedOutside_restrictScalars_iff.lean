-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_restrictScalars_iff
-- name    : GroundTheory.ProfCoh.isUnramifiedOutside_restrictScalars_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:00.303883+00:00
-- url     : https://prove2.me/theorems/46b6730a-2567-5392-9f4e-a64497543fe3
-- title:
--   Prof Coh: is Unramified Outside restrict Scalars iff
-- statement:
--   The Prof Coh construction uses the is Unramified Outside restrict Scalars iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L112-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L112-L142

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

theorem GroundTheory.ProfCoh.isUnramifiedOutside_restrictScalars_iff {L : IntermediateField F Ω} [FiniteDimensional F L]
    (hL : IsUnramifiedOutside S L) (M : IntermediateField L Ω) [FiniteDimensional L M] :
    IsUnramifiedOutside S (M.restrictScalars F) ↔ IsUnramifiedOutside (placesOver S) M := by sorry
