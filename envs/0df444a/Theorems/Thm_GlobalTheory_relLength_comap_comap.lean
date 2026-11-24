-- Prove2me | Theorems.Thm_GlobalTheory_relLength_comap_comap
-- name    : GlobalTheory.relLength_comap_comap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:04.506036+00:00
-- url     : https://prove2.me/theorems/a9b019fc-424b-4d4b-b237-05526afb11ca
-- title:
--   Global Theory: rel Length comap comap
-- statement:
--   The Global Theory construction uses the rel Length comap comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L175-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} [RingHomSurjective σ]

theorem GlobalTheory.relLength_comap_comap (f : V →ₛₗ[σ] V') (A' B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength (LinearMap.range f ⊓ A') B' := by sorry
