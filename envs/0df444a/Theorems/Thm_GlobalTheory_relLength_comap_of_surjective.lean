-- Prove2me | Theorems.Thm_GlobalTheory_relLength_comap_of_surjective
-- name    : GlobalTheory.relLength_comap_of_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:20.097688+00:00
-- url     : https://prove2.me/theorems/d8e39f27-a35e-4968-bd7b-0e501448342f
-- title:
--   Global Theory: rel Length comap of surjective
-- statement:
--   The Global Theory construction uses the rel Length comap of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L188-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L188-L190

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

theorem GlobalTheory.relLength_comap_of_surjective (f : V →ₛₗ[σ] V') (hf : Function.Surjective f)
    (A' B' : Submodule S V') : relLength (A'.comap f) (B'.comap f) = relLength A' B' := by sorry
