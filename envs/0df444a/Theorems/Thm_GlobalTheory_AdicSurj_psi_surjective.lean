-- Prove2me | Theorems.Thm_GlobalTheory_AdicSurj_psi_surjective
-- name    : GlobalTheory.AdicSurj.psi_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:54:33.608312+00:00
-- url     : https://prove2.me/theorems/260da83a-2cc6-4aa0-b08d-23b059ce2162
-- title:
--   Adic Surj: psi surjective
-- statement:
--   The Adic Surj construction uses the psi surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L59-L72

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

theorem GlobalTheory.AdicSurj.psi_surjective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Surjective (psi B J) := by sorry
