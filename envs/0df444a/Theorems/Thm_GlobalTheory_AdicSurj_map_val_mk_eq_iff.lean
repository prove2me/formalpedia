-- Prove2me | Theorems.Thm_GlobalTheory_AdicSurj_map_val_mk_eq_iff
-- name    : GlobalTheory.AdicSurj.map_val_mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:55.570149+00:00
-- url     : https://prove2.me/theorems/e4d4ab2f-2228-4451-a5ea-fc2e365a7c3d
-- title:
--   Adic Surj: map val mk eq iff
-- statement:
--   The Adic Surj construction uses the map val mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L52-L57

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

theorem GlobalTheory.AdicSurj.map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : B) :
    (map J (Algebra.linearMap A B) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by sorry
