-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_subset_of_subset_maxUnramifiedOutside
-- name    : GroundTheory.ProfCoh.exists_subset_of_subset_maxUnramifiedOutside
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:20.6721+00:00
-- url     : https://prove2.me/theorems/7a8ad4d1-b6a2-4aa1-8f41-67ac6f675043
-- title:
--   Prof Coh: exists subset of subset max Unramified Outside
-- statement:
--   The Prof Coh construction uses the exists subset of subset max Unramified Outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L54-L68

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

theorem GroundTheory.ProfCoh.exists_subset_of_subset_maxUnramifiedOutside (s : Finset Ω)
    (hs : ∀ x ∈ s, x ∈ maxUnramifiedOutside F Ω S) :
    ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
      ∀ x ∈ s, x ∈ E := by sorry
