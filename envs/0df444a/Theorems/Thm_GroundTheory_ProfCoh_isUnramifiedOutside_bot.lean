-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_bot
-- name    : GroundTheory.ProfCoh.isUnramifiedOutside_bot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:40.935949+00:00
-- url     : https://prove2.me/theorems/ccac1c1d-f9cc-457a-af77-52dadbf5e64a
-- title:
--   Prof Coh: is Unramified Outside bot
-- statement:
--   The Prof Coh construction uses the is Unramified Outside bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L111-L113

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

theorem GroundTheory.ProfCoh.isUnramifiedOutside_bot (S : Set (HeightOneSpectrum (𝓞 F))) :
    IsUnramifiedOutside S (⊥ : IntermediateField F Ω) := by sorry
