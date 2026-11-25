-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_map
-- name    : GroundTheory.ProfCoh.isUnramifiedIn_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:41.283063+00:00
-- url     : https://prove2.me/theorems/cc0ff791-be9e-4252-a3df-71a2de265371
-- title:
--   Prof Coh: is Unramified In map
-- statement:
--   The Prof Coh construction uses the is Unramified In map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L115-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L115-L145

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]

theorem GroundTheory.ProfCoh.isUnramifiedIn_map {E : IntermediateField F Ω} [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) (hE : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) (τ : Gal(Ω/F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (τ : Ω →ₐ[F] Ω))) v.asIdeal := by sorry
