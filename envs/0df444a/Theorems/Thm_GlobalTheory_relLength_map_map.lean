-- Prove2me | Theorems.Thm_GlobalTheory_relLength_map_map
-- name    : GlobalTheory.relLength_map_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:17.779315+00:00
-- url     : https://prove2.me/theorems/526e4dec-c2cf-40cd-bb44-8f89cd0249b2
-- title:
--   Global Theory: rel Length map map
-- statement:
--   The Global Theory construction uses the rel Length map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L171-L173

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

theorem GlobalTheory.relLength_map_map (f : V →ₛₗ[σ] V') (A B : Submodule R V) :
    relLength (A.map f) (B.map f) = relLength A (B ⊔ LinearMap.ker f) := by sorry
