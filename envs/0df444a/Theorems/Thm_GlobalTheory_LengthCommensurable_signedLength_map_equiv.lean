-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_map_equiv
-- name    : GlobalTheory.LengthCommensurable.signedLength_map_equiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:17.755332+00:00
-- url     : https://prove2.me/theorems/ad857375-fb07-44ef-a96d-61d6eb3f5406
-- title:
--   Length Commensurable: signed Length map equiv
-- statement:
--   The Length Commensurable construction uses the signed Length map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L223-L226

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

theorem GlobalTheory.LengthCommensurable.signedLength_map_equiv {A B : Submodule R V}
    (h : LengthCommensurable A B) (e : V ≃ₛₗ[σ] V') :
    signedLength (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) = signedLength A B := by sorry
