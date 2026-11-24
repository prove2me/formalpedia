-- Prove2me | Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_tprod
-- name    : GlobalTheory.bijective_toSpanSingleton_tprod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:37.225614+00:00
-- url     : https://prove2.me/theorems/2620b3b6-9281-401b-b5db-2dc2d1df7a08
-- title:
--   Global Theory: bijective to Span Singleton tprod
-- statement:
--   The Global Theory construction uses the bijective to Span Singleton tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L497-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L497-L524

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
variable {A : Type*} [CommRing A]

theorem GlobalTheory.bijective_toSpanSingleton_tprod {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (e : ∀ i, M i)
    (he : ∀ i, Function.Bijective (LinearMap.toSpanSingleton A (M i) (e i))) :
    Function.Bijective
      (LinearMap.toSpanSingleton A (⨂[A] i, M i) (PiTensorProduct.tprod A e)) := by sorry
