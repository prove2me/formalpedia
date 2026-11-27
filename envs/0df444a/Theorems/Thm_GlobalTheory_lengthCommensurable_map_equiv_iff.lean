-- Prove2me | Theorems.Thm_GlobalTheory_lengthCommensurable_map_equiv_iff
-- name    : GlobalTheory.lengthCommensurable_map_equiv_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:40.804283+00:00
-- url     : https://prove2.me/theorems/dfdc8efa-f14b-4781-b90a-b9c09df7606c
-- title:
--   Global Theory: length Commensurable map equiv iff
-- statement:
--   The Global Theory construction uses the length Commensurable map equiv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L218-L221

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
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [RingHomSurjective σ]

theorem GlobalTheory.lengthCommensurable_map_equiv_iff (e : V ≃ₛₗ[σ] V') {A B : Submodule R V} :
    LengthCommensurable (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) ↔
      LengthCommensurable A B := by sorry
