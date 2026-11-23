-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_map_of_injective
-- name    : GlobalTheory.LengthCommensurable.signedLength_map_of_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:26.697343+00:00
-- url     : https://prove2.me/theorems/6d41be9e-f4d9-4e81-95d4-e1b4fc188481
-- title:
--   Length Commensurable: signed Length map of injective
-- statement:
--   The Length Commensurable construction uses the signed Length map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L197-L200

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

theorem GlobalTheory.LengthCommensurable.signedLength_map_of_injective {A B : Submodule R V}
    (_h : LengthCommensurable A B) (f : V →ₛₗ[σ] V') (hf : Function.Injective f) :
    signedLength (A.map f) (B.map f) = signedLength A B := by sorry
