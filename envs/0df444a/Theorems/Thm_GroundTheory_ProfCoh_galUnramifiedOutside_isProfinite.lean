-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_galUnramifiedOutside_isProfinite
-- name    : GroundTheory.ProfCoh.galUnramifiedOutside_isProfinite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:59.950898+00:00
-- url     : https://prove2.me/theorems/4f9b5a3a-9ed9-4b38-b2be-df61d17d0202
-- title:
--   Prof Coh: gal Unramified Outside is Profinite
-- statement:
--   The Prof Coh construction uses the gal Unramified Outside is Profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean#L101-L104

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

theorem GroundTheory.ProfCoh.galUnramifiedOutside_isProfinite :
    CompactSpace (galUnramifiedOutside F Ω S) ∧ T2Space (galUnramifiedOutside F Ω S) ∧
      TotallyDisconnectedSpace (galUnramifiedOutside F Ω S) := by sorry
