-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_sup
-- name    : GroundTheory.ProfCoh.IsUnramifiedOutside.sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:59.637452+00:00
-- url     : https://prove2.me/theorems/465741b0-966c-4656-892e-a8933e437988
-- title:
--   Is Unramified Outside: sup
-- statement:
--   The Is Unramified Outside construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L98-L101

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

theorem GroundTheory.ProfCoh.IsUnramifiedOutside.sup {S : Set (HeightOneSpectrum (𝓞 F))} {E₁ E₂ : IntermediateField F Ω}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂] (h₁ : IsUnramifiedOutside S E₁)
    (h₂ : IsUnramifiedOutside S E₂) : IsUnramifiedOutside S (E₁ ⊔ E₂) := by sorry
