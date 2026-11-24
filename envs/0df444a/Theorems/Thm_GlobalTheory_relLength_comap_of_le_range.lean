-- Prove2me | Theorems.Thm_GlobalTheory_relLength_comap_of_le_range
-- name    : GlobalTheory.relLength_comap_of_le_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:47.162616+00:00
-- url     : https://prove2.me/theorems/71cdd575-f4e4-4a7d-9e29-e9adeb13db19
-- title:
--   Global Theory: rel Length comap of le range
-- statement:
--   The Global Theory construction uses the rel Length comap of le range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L183-L186

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

theorem GlobalTheory.relLength_comap_of_le_range (f : V →ₛₗ[σ] V') {A' : Submodule S V'}
    (hA : A' ≤ LinearMap.range f) (B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength A' B' := by sorry
