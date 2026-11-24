-- Prove2me | Theorems.Thm_GlobalTheory_span_image_invariants
-- name    : GlobalTheory.span_image_invariants
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:16.931856+00:00
-- url     : https://prove2.me/theorems/9d252c3f-99e0-4b16-8b5c-fa9f92e19fde
-- title:
--   Global Theory: span image invariants
-- statement:
--   The Global Theory construction uses the span image invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L183-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L183-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]

theorem GlobalTheory.span_image_invariants [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (ρ' : Representation S G M') (f : M →ₗ[R] M') (hb : IsBaseChange S f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    Submodule.span S (f '' ρ.invariants) = ρ'.invariants := by sorry
