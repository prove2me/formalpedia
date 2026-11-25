-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_sup
-- name    : GroundTheory.ProfCoh.isUnramifiedIn_sup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:09.292827+00:00
-- url     : https://prove2.me/theorems/dced1712-3cb4-44e1-a49f-c2f2098e7467
-- title:
--   Prof Coh: is Unramified In sup
-- statement:
--   The Prof Coh construction uses the is Unramified In sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L88-L96

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

theorem GroundTheory.ProfCoh.isUnramifiedIn_sup {E₁ E₂ : IntermediateField F Ω} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] (v : HeightOneSpectrum (𝓞 F))
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) v.asIdeal) (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) v.asIdeal := by sorry
