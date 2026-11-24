-- Prove2me | Theorems.Thm_GlobalTheory_AdicSurj_ker_psi
-- name    : GlobalTheory.AdicSurj.ker_psi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:55:09.144882+00:00
-- url     : https://prove2.me/theorems/7f7cc2e7-1199-4ee6-b64f-083e72fed269
-- title:
--   Adic Surj: ker psi
-- statement:
--   The Adic Surj construction uses the ker psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L74-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L74-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicSurj
open AdicCompletion
variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem GlobalTheory.AdicSurj.ker_psi [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    RingHom.ker (psi B J) =
      Ideal.map (algebraMap A (AdicCompletion J A)) (LinearMap.ker (Algebra.linearMap A B)) := by sorry
