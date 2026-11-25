-- Prove2me | Theorems.Thm_GlobalTheory_T_nonempty_adicCompletion_tensor_ringEquiv_of_surjective
-- name    : GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:15.288926+00:00
-- url     : https://prove2.me/theorems/220b5def-316b-52ca-ab59-d506b47c80bb
-- title:
--   T: nonempty adic Completion tensor ring Equiv of surjective
-- statement:
--   The T construction uses the nonempty adic Completion tensor ring Equiv of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquivStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquivStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective : ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R] [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K], Function.Surjective (algebraMap R₀ R) → Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+* AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by sorry
