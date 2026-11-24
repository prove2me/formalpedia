-- Prove2me | Theorems.Thm_GlobalTheory_AdicSurj_theta_bijective
-- name    : GlobalTheory.AdicSurj.theta_bijective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:54:46.926121+00:00
-- url     : https://prove2.me/theorems/6b9ec6b4-6ad3-4595-afb8-3ca6f8a65588
-- title:
--   Adic Surj: theta bijective
-- statement:
--   The Adic Surj construction uses the theta bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L126-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L126-L162

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
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem GlobalTheory.AdicSurj.theta_bijective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Bijective (theta (B := B) J) := by sorry
