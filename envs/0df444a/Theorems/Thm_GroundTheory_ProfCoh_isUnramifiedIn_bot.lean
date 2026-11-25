-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_bot
-- name    : GroundTheory.ProfCoh.isUnramifiedIn_bot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:45.422697+00:00
-- url     : https://prove2.me/theorems/30552556-7ac5-42ef-96cf-c1490da69d7a
-- title:
--   Prof Coh: is Unramified In bot
-- statement:
--   The Prof Coh construction uses the is Unramified In bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L103-L109

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

theorem GroundTheory.ProfCoh.isUnramifiedIn_bot (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⊥ : IntermediateField F Ω)) v.asIdeal := by sorry
